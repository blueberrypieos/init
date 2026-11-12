/*
 * SPDX-License-Identifier: BSD-2-Clause
 * Copyright (c) 2026 The Blueberry Pie OS Authors
 *
 * init: Blueberry Pie OS's process 1, installed as /sbin/launchd (the program
 * xnu starts). It is a small classic init that is also the bootstrap server:
 *
 *   - puts the console on standard input, output and error;
 *   - remounts the root filesystem read-write;
 *   - serves the task bootstrap port that every process inherits: services
 *     check in, look up and register by name, and root can ask for a
 *     reboot or halt (the protocol of <pie/bootstrap.h>, which libxpc's
 *     bootstrap_* calls and reboot3() speak); only root may serve a
 *     system name, one that starts with SYSTEM_PREFIX, or a host port
 *     name; a name is forgotten once its service's port dies (its owner
 *     exited), so that it can be checked in again and names made up at
 *     run time do not pile up;
 *   - makes the ports of the host port names at boot and sets them as the
 *     host's special ports, as launchd's HostSpecialPort does: auditd
 *     checks in com.apple.auditd, the kernel's audit control port;
 *   - runs /etc/rc (with /bin/sh), then keeps getty on the console,
 *     starting a new one when it exits, or a root shell without login;
 *   - on a reboot or halt, runs /etc/rc.shutdown (with /bin/sh) while it
 *     still serves the bootstrap port, for RC_SHUTDOWN_WAIT seconds at
 *     most, then stops every process;
 *   - reaps every orphaned process.
 *
 * xnu lets no process signal init, so reboot(8) and shutdown(8) ask it
 * over the bootstrap port. Signals from the kernel (SIGTERM, SIGUSR2)
 * still reboot and halt.
 */
#include <bsm/libbsm.h>
#include <errno.h>
#include <fcntl.h>
#include <hfs/hfs_mount.h>
#include <mach/host_special_ports.h>
#include <mach/mach.h>
#include <mach/notify.h>
#include <paths.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/event.h>
#include <sys/ioctl.h>
#include <sys/mount.h>
#include <sys/reboot.h>
#include <sys/stat.h>
#include <sys/vnode.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>
#include <pie/bootstrap.h>

#define SHELL            "/bin/sh"
#define RC               "/etc/rc"
#define RC_SHUTDOWN      "/etc/rc.shutdown"
#define RC_SHUTDOWN_WAIT 30
#define GETTY            "/usr/libexec/getty"
#define LOGIN            "/usr/bin/login"
#define CONSOLE          _PATH_CONSOLE
#define ROOT_HOME        "/var/root"
#define PATH             "/usr/bin:/bin:/usr/sbin:/sbin"

static int shutdown_how = -1;         /* RB_* once a reboot or halt is asked for */
static pid_t rc_pid, console_pid, rc_shutdown_pid;
static mach_port_t bs_port;
static mach_port_t bs_notify;           /* dead-name notifications; no one else can send here */
static int kq;

enum { TIMER_CONSOLE = 1, TIMER_RC_SHUTDOWN };

static void
say(const char *fmt, ...)
{
	va_list ap;
	char buf[256];
	va_start(ap, fmt);
	int n = vsnprintf(buf, sizeof(buf), fmt, ap);
	va_end(ap);
	if (n > 0) {
		write(STDERR_FILENO, "init: ", 6);
		write(STDERR_FILENO, buf, (size_t)n < sizeof(buf) ? (size_t)n : sizeof(buf) - 1);
		write(STDERR_FILENO, "\n", 1);
	}
}

/* Open the console as standard input, output and error. */
static void
open_console(void)
{
	int fd = open(CONSOLE, O_RDWR | O_NOCTTY);
	if (fd < 0) {
		return;
	}
	dup2(fd, STDIN_FILENO);
	dup2(fd, STDOUT_FILENO);
	dup2(fd, STDERR_FILENO);
	if (fd > STDERR_FILENO) {
		close(fd);
	}
}

/* The kernel mounts the root read-only; make it writable. */
static void
remount_root(void)
{
	struct statfs sfs;
	if (statfs("/", &sfs) != 0) {
		say("statfs /: %s", strerror(errno));
		return;
	}
	if (!(sfs.f_flags & MNT_RDONLY)) {
		return;
	}
	int r;
	if (strcmp(sfs.f_fstypename, "hfs") == 0) {
		/*
		 * hfs_mount() needs its arguments on an update; VNOVAL: no
		 * change. The device path only renames the mount: the kernel
		 * mounted the root as "root_device", and quotacheck, fsck and df
		 * want its /dev name. Without one, the update keeps the name.
		 */
		struct hfs_mount_args args;
		struct stat st;
		char dev[MAXPATHLEN];
		const char *name;
		memset(&args, 0, sizeof(args));
		args.fspec = NULL;
		if (stat("/", &st) == 0 && (name = devname(st.st_dev, S_IFBLK)) != NULL) {
			snprintf(dev, sizeof(dev), "/dev/%s", name);
			args.fspec = dev;
		}
		args.hfs_uid = (uid_t)VNOVAL;
		args.hfs_gid = (gid_t)VNOVAL;
		args.hfs_mask = (mode_t)VNOVAL;
		args.hfs_encoding = (u_int32_t)VNOVAL;
		args.hfs_timezone.tz_minuteswest = VNOVAL;
		args.hfs_timezone.tz_dsttime = VNOVAL;
		args.flags = VNOVAL;
		r = mount(sfs.f_fstypename, "/", (int)(sfs.f_flags & ~MNT_RDONLY) | MNT_UPDATE, &args);
	} else {
		r = mount(sfs.f_fstypename, "/", (int)(sfs.f_flags & ~MNT_RDONLY) | MNT_UPDATE, NULL);
	}
	if (r != 0) {
		say("cannot mount / (%s, %s) read-write: %s", sfs.f_mntfromname,
		    sfs.f_fstypename, strerror(errno));
	}
}

static void
setup_environment(void)
{
	setenv("PATH", PATH, 1);
	setenv("HOME", ROOT_HOME, 1);
	setenv("SHELL", SHELL, 1);
	setenv("USER", "root", 1);
	setenv("LOGNAME", "root", 1);
	setenv("TERM", "vt100", 0);
}

/* --- processes ------------------------------------------------------------------ */

/* Start `path` in a new session that owns the console (opened with `oflags` too). */
static pid_t
spawn_on_console(const char *dir, const char *path, char *const argv[], int oflags)
{
	pid_t pid = fork();
	if (pid != 0) {
		if (pid < 0) {
			say("fork: %s", strerror(errno));
		}
		return pid;
	}
	setsid();
	int fd = open(CONSOLE, O_RDWR | oflags);
	if (fd >= 0) {
		dup2(fd, STDIN_FILENO);
		dup2(fd, STDOUT_FILENO);
		dup2(fd, STDERR_FILENO);
		if (fd > STDERR_FILENO) {
			close(fd);
		}
		ioctl(STDIN_FILENO, TIOCSCTTY, 0);
		tcsetpgrp(STDIN_FILENO, getpid());
	}
	for (int sig = 1; sig < NSIG; sig++) {
		signal(sig, SIG_DFL);
	}
	sigset_t none;
	sigemptyset(&none);
	sigprocmask(SIG_SETMASK, &none, NULL);
	chdir(dir);
	execv(path, argv);
	say("cannot run %s: %s", path, strerror(errno));
	_exit(127);
}

static void restart_console_later(void);

static void
start_console(void)
{
	char *getty_argv[] = { "getty", "default", "-", NULL };
	char *shell_argv[] = { "-sh", NULL };
	const char *path = GETTY;
	char **argv = getty_argv;
	if (access(GETTY, X_OK) != 0 || access(LOGIN, X_OK) != 0) {
		path = SHELL;
		argv = shell_argv;
		say("getty or login unavailable; starting a root shell");
	}
	/*
	 * Getty's "-" uses the console descriptors and controlling terminal
	 * set up by spawn_on_console(). The default entry keeps its speed.
	 *
	 * O_POPUP: the screen of a boot without -v (pieboot's pie, the
	 * kernel's progress bar), which /etc/rc ran behind, turns into the
	 * text console for login or the fallback shell.
	 */
	console_pid = spawn_on_console(ROOT_HOME, path, argv, O_POPUP);
	if (console_pid < 0) {
		console_pid = 0;
		restart_console_later();
	}
}

/* Start a new console process in a second (it may keep exiting at once). */
static void
restart_console_later(void)
{
	struct kevent ev;
	EV_SET(&ev, TIMER_CONSOLE, EVFILT_TIMER, EV_ADD | EV_ONESHOT, NOTE_SECONDS, 1, NULL);
	kevent(kq, &ev, 1, NULL, 0, NULL);
}

static void
reap(void)
{
	int status;
	pid_t pid;
	while ((pid = waitpid(-1, &status, WNOHANG)) > 0) {
		if (pid == rc_pid) {
			rc_pid = 0;
			if (status != 0) {
				say("%s exited with status %d", RC,
				    WIFEXITED(status) ? WEXITSTATUS(status) : -1);
			}
			if (shutdown_how < 0) {
				start_console();
			}
		} else if (pid == rc_shutdown_pid) {
			rc_shutdown_pid = 0;
			if (status != 0) {
				say("%s exited with status %d", RC_SHUTDOWN,
				    WIFEXITED(status) ? WEXITSTATUS(status) : -1);
			}
		} else if (pid == console_pid) {
			console_pid = 0;
			if (shutdown_how < 0) {
				say("console process exited; starting a new one");
				restart_console_later();
			}
		}
	}
}

/* --- the bootstrap server ----------------------------------------------------------- */

/*
 * A name's service. A name is made by its first check-in or register. A
 * check-in makes a port and hands its receive right to the service in the
 * reply; a register gives init a send right to the service's own port. A
 * look-up only finds a name and never makes one. Once the receive right is
 * the service's, or a send right was registered, init asks for a dead-name
 * notification on its send right: when the port dies (the process holding
 * the receive right exited), the name is forgotten.
 *
 * Clients trust whoever serves a system name, so only a sender whose audit
 * token has euid 0 may check one in or register one.
 */
#define SYSTEM_PREFIX "com.apple.system."

/*
 * Names whose port is also a host special port. Only the kernel and init may
 * set one, so init makes the port: at boot, and again for a check-in once the
 * previous port has died. The kernel can send to it before the service checks
 * in. Only root may check one in. None may be registered, as the host's
 * special port would stay the old one, and none may be looked up: its
 * service may not check who sends to it, and root reaches it as the host
 * special port.
 */
static const struct {
	const char *name;
	int id;
} host_ports[] = {
	{ "com.apple.auditd", HOST_AUDIT_CONTROL_PORT },
};

struct service {
	struct service *next;
	name_t name;
	mach_port_t send;       /* our send right to the service */
	mach_port_t recv;       /* its receive right, until the service checks in */
};
static struct service *services;

static int
host_port_id(const char *name)
{
	for (size_t i = 0; i < sizeof(host_ports) / sizeof(host_ports[0]); i++) {
		if (strcmp(name, host_ports[i].name) == 0) {
			return host_ports[i].id;
		}
	}
	return 0;
}

static bool
privileged_name(const char *name)
{
	return strncmp(name, SYSTEM_PREFIX, sizeof(SYSTEM_PREFIX) - 1) == 0 || host_port_id(name) != 0;
}

static struct service *
find_service(const char *name)
{
	for (struct service *s = services; s != NULL; s = s->next) {
		if (strcmp(s->name, name) == 0) {
			return s;
		}
	}
	return NULL;
}

static struct service *
new_service(const char *name)
{
	struct service *s = calloc(1, sizeof(*s));
	if (s == NULL) {
		return NULL;
	}
	strlcpy(s->name, name, sizeof(s->name));
	s->next = services;
	services = s;
	return s;
}

/*
 * Make a service's port, for its check-in: the receive right and our send
 * right under one name. A host port name's port becomes that host special port.
 */
static kern_return_t
new_port(struct service *s)
{
	mach_port_t self = mach_task_self(), port;
	kern_return_t kr = mach_port_allocate(self, MACH_PORT_RIGHT_RECEIVE, &port);
	if (kr != KERN_SUCCESS) {
		return kr;
	}
	mach_port_insert_right(self, port, port, MACH_MSG_TYPE_MAKE_SEND);
	s->send = s->recv = port;
	int id = host_port_id(s->name);
	if (id != 0) {
		mach_port_t host = mach_host_self();
		kr = host_set_special_port(host, id, port);
		mach_port_deallocate(self, host);
		if (kr != KERN_SUCCESS) {
			say("cannot set host port %d for %s: %s", id, s->name, mach_error_string(kr));
		}
	}
	return KERN_SUCCESS;
}

/* Forget a service: unlink it and drop our right to its port. */
static void
remove_service(struct service *s)
{
	mach_port_t self = mach_task_self();
	for (struct service **p = &services; *p != NULL; p = &(*p)->next) {
		if (*p == s) {
			*p = s->next;
			break;
		}
	}
	if (MACH_PORT_VALID(s->recv)) {
		/*
		 * Never checked in: the port is ours, send and receive under one
		 * name, which is a dead name once the receive right is gone.
		 */
		mach_port_mod_refs(self, s->recv, MACH_PORT_RIGHT_RECEIVE, -1);
	}
	if (MACH_PORT_VALID(s->send)) {
		mach_port_deallocate(self, s->send);
	}
	free(s);
}

/* Whether a service's port is gone: our send right to it is a dead name. */
static bool
service_dead(const struct service *s)
{
	mach_port_type_t type;
	if (MACH_PORT_VALID(s->recv)) {
		return false;
	}
	return !MACH_PORT_VALID(s->send) ||
	       mach_port_type(mach_task_self(), s->send, &type) != KERN_SUCCESS ||
	       (type & MACH_PORT_TYPE_DEAD_NAME);
}

/*
 * Ask for a dead-name notification on a service's send right (once the
 * service holds the receive right). If the port has died already, the
 * service goes now. A name that several services share (one port
 * registered under more than one name) has one request: asking again
 * replaces it, and the notification forgets all of them.
 */
static void
watch_service(struct service *s)
{
	mach_port_t self = mach_task_self(), previous = MACH_PORT_NULL;
	if (bs_notify == MACH_PORT_NULL || MACH_PORT_VALID(s->recv) || !MACH_PORT_VALID(s->send)) {
		return;
	}
	kern_return_t kr = mach_port_request_notification(self, s->send, MACH_NOTIFY_DEAD_NAME, 0,
	    bs_notify, MACH_MSG_TYPE_MAKE_SEND_ONCE, &previous);
	if (kr == KERN_SUCCESS) {
		if (MACH_PORT_VALID(previous)) {
			mach_port_deallocate(self, previous);
		}
	} else if (service_dead(s)) {
		remove_service(s);
	} else {
		say("cannot watch service %s: %s", s->name, mach_error_string(kr));
	}
}

/* Serve the notifications that are waiting: forget the services whose ports died. */
static void
bs_notify_drain(void)
{
	mach_port_t self = mach_task_self();
	for (;;) {
		union {
			mach_msg_header_t head;
			mach_dead_name_notification_t dead;
			uint8_t buf[sizeof(mach_dead_name_notification_t) + MAX_TRAILER_SIZE];
		} in;
		kern_return_t kr = mach_msg(&in.head, MACH_RCV_MSG | MACH_RCV_TIMEOUT | MACH_RCV_LARGE, 0,
		    sizeof(in), bs_notify, 0, MACH_PORT_NULL);
		if (kr == MACH_RCV_TOO_LARGE) {
			/* Not a notification we asked for: receive it whole and drop it. */
			mach_msg_size_t size = in.head.msgh_size + MAX_TRAILER_SIZE;
			mach_msg_header_t *big = malloc(size);
			if (big == NULL || mach_msg(big, MACH_RCV_MSG | MACH_RCV_TIMEOUT, 0, size, bs_notify, 0,
			    MACH_PORT_NULL) != KERN_SUCCESS) {
				free(big);
				return;
			}
			mach_msg_destroy(big);
			free(big);
			continue;
		}
		if (kr != KERN_SUCCESS) {
			return;
		}
		if (in.head.msgh_id != MACH_NOTIFY_DEAD_NAME ||
		    in.head.msgh_size < offsetof(mach_dead_name_notification_t, trailer)) {
			/* Port-deleted and send-once notifications: nothing to do. */
			mach_msg_destroy(&in.head);
			continue;
		}
		mach_port_t name = in.dead.not_port;
		struct service *s = services;
		while (s != NULL) {
			struct service *next = s->next;
			if (s->send == name && !MACH_PORT_VALID(s->recv)) {
				remove_service(s);
			}
			s = next;
		}
		/* The notification's own reference on the dead name. */
		mach_port_deallocate(self, name);
	}
}

static void
bs_setup(void)
{
	mach_port_t self = mach_task_self();
	if (mach_port_allocate(self, MACH_PORT_RIGHT_RECEIVE, &bs_port) != KERN_SUCCESS ||
	    mach_port_insert_right(self, bs_port, bs_port, MACH_MSG_TYPE_MAKE_SEND) != KERN_SUCCESS ||
	    task_set_special_port(self, TASK_BOOTSTRAP_PORT, bs_port) != KERN_SUCCESS) {
		say("cannot set up the bootstrap port");
		bs_port = MACH_PORT_NULL;
		return;
	}
	/*
	 * Children inherit the port. init keeps its bootstrap_port variable as
	 * the kernel gave it (none), so its own library calls never ask
	 * itself and wait for an answer forever.
	 */
	struct kevent ev[2];
	int n = 0;
	EV_SET(&ev[n++], bs_port, EVFILT_MACHPORT, EV_ADD, 0, 0, NULL);
	/* Only the kernel sends here (through send-once rights init makes). */
	if (mach_port_allocate(self, MACH_PORT_RIGHT_RECEIVE, &bs_notify) == KERN_SUCCESS) {
		EV_SET(&ev[n++], bs_notify, EVFILT_MACHPORT, EV_ADD, 0, 0, NULL);
	} else {
		say("cannot make the bootstrap notification port; names stay after their services exit");
		bs_notify = MACH_PORT_NULL;
	}
	kevent(kq, ev, n, NULL, 0, NULL);

	for (size_t i = 0; i < sizeof(host_ports) / sizeof(host_ports[0]); i++) {
		struct service *s = new_service(host_ports[i].name);
		if (s == NULL || new_port(s) != KERN_SUCCESS) {
			say("cannot make the port of %s", host_ports[i].name);
		}
	}
}

static void
bs_handle(pie_bs_request_buffer_t *in)
{
	pie_bs_request_t *req = &in->req;
	pie_bs_reply_t rep;
	mach_port_t self = mach_task_self();

	if (req->head.msgh_size != sizeof(*req) || !(req->head.msgh_bits & MACH_MSGH_BITS_COMPLEX) ||
	    MACH_MSGH_BITS_REMOTE(req->head.msgh_bits) != MACH_MSG_TYPE_PORT_SEND_ONCE ||
	    req->body.msgh_descriptor_count != 1 || req->port.type != MACH_MSG_PORT_DESCRIPTOR ||
	    (MACH_PORT_VALID(req->port.name) && req->port.disposition != MACH_MSG_TYPE_PORT_SEND)) {
		mach_msg_destroy(&req->head);
		return;
	}
	mach_port_t passed = req->port.name;
	req->name[sizeof(req->name) - 1] = '\0';
	/* The sender's credentials, from the audit trailer. */
	mach_msg_audit_trailer_t *trailer =
	    (mach_msg_audit_trailer_t *)((uint8_t *)req + round_msg(req->head.msgh_size));
	uid_t euid;
	audit_token_to_au32(trailer->msgh_audit, NULL, &euid, NULL, NULL, NULL, NULL, NULL, NULL);

	memset(&rep, 0, sizeof(rep));
	rep.head.msgh_bits = MACH_MSGH_BITS_SET(MACH_MSGH_BITS_REMOTE(req->head.msgh_bits), 0, 0,
	    MACH_MSGH_BITS_COMPLEX);
	rep.head.msgh_remote_port = req->head.msgh_remote_port;
	rep.head.msgh_size = sizeof(rep);
	rep.head.msgh_id = req->head.msgh_id + PIE_BS_REPLY;
	rep.body.msgh_descriptor_count = 1;
	rep.port.type = MACH_MSG_PORT_DESCRIPTOR;
	rep.port.name = MACH_PORT_NULL;
	rep.port.disposition = MACH_MSG_TYPE_COPY_SEND;
	rep.ret = KERN_SUCCESS;

	struct service *s = find_service(req->name);
	if (s != NULL && service_dead(s)) {
		/* Its notification is on its way; forget it now. */
		remove_service(s);
		s = NULL;
	}
	struct service *watch = NULL;   /* a service to watch once the reply has gone */
	switch (req->head.msgh_id) {
	case PIE_BS_CHECK_IN:
		if (euid != 0 && privileged_name(req->name)) {
			rep.ret = BOOTSTRAP_NOT_PRIVILEGED;
			break;
		}
		if (s == NULL && ((s = new_service(req->name)) == NULL || new_port(s) != KERN_SUCCESS)) {
			rep.ret = BOOTSTRAP_NO_MEMORY;
			break;
		}
		if (s->recv == MACH_PORT_NULL) {
			rep.ret = BOOTSTRAP_SERVICE_ACTIVE;
		} else {
			rep.port.name = s->recv;
			rep.port.disposition = MACH_MSG_TYPE_MOVE_RECEIVE;
			s->recv = MACH_PORT_NULL;
			watch = s;
		}
		break;
	case PIE_BS_LOOK_UP:
		if (host_port_id(req->name) != 0) {
			rep.ret = BOOTSTRAP_NOT_PRIVILEGED;
		} else if (s == NULL || !MACH_PORT_VALID(s->send)) {
			rep.ret = BOOTSTRAP_UNKNOWN_SERVICE;
		} else {
			rep.port.name = s->send;
		}
		break;
	case PIE_BS_REGISTER:
		if (!MACH_PORT_VALID(passed) || (euid != 0 && privileged_name(req->name)) ||
		    host_port_id(req->name) != 0) {
			rep.ret = BOOTSTRAP_NOT_PRIVILEGED;
		} else if (s != NULL && s->recv == MACH_PORT_NULL && euid != 0) {
			/* Only root replaces a service that has checked in. */
			rep.ret = BOOTSTRAP_NAME_IN_USE;
		} else if (s == NULL && (s = new_service(req->name)) == NULL) {
			rep.ret = BOOTSTRAP_NO_MEMORY;
		} else {
			if (MACH_PORT_VALID(s->recv)) {
				/* Not checked in yet: the port we made goes away. */
				mach_port_mod_refs(self, s->recv, MACH_PORT_RIGHT_RECEIVE, -1);
				s->recv = MACH_PORT_NULL;
			}
			if (MACH_PORT_VALID(s->send)) {
				mach_port_deallocate(self, s->send);
			}
			s->send = passed;
			passed = MACH_PORT_NULL;
			watch = s;
		}
		break;
	case PIE_BS_REBOOT:
		if (euid != 0) {
			rep.ret = BOOTSTRAP_NOT_PRIVILEGED;
		} else if (shutdown_how < 0) {
			shutdown_how = (req->arg & RB_HALT) ? RB_HALT : RB_AUTOBOOT;
		}
		break;
	default:
		rep.ret = MIG_BAD_ID;
		break;
	}
	if (MACH_PORT_VALID(passed)) {
		mach_port_deallocate(self, passed);
	}
	/* The reply port is a send-once right: sending to it never blocks. */
	if (mach_msg(&rep.head, MACH_SEND_MSG, sizeof(rep), 0, MACH_PORT_NULL, MACH_MSG_TIMEOUT_NONE,
	    MACH_PORT_NULL) != KERN_SUCCESS) {
		/* A receive right that did not go dies here: watch_service sees it. */
		mach_msg_destroy(&rep.head);
	}
	if (watch != NULL) {
		watch_service(watch);
	}
}

/* Serve every request that is waiting. */
static void
bs_drain(void)
{
	for (;;) {
		pie_bs_request_buffer_t in;
		kern_return_t kr = mach_msg(&in.req.head,
		    MACH_RCV_MSG | MACH_RCV_TIMEOUT | MACH_RCV_LARGE |
		    MACH_RCV_TRAILER_TYPE(MACH_MSG_TRAILER_FORMAT_0) |
		    MACH_RCV_TRAILER_ELEMENTS(MACH_RCV_TRAILER_AUDIT),
		    0, sizeof(in), bs_port, 0, MACH_PORT_NULL);
		if (kr == MACH_RCV_TOO_LARGE) {
			/* Not ours: receive it into a big enough buffer and drop it. */
			mach_msg_size_t size = in.req.head.msgh_size + MAX_TRAILER_SIZE;
			mach_msg_header_t *big = malloc(size);
			if (big == NULL || mach_msg(big, MACH_RCV_MSG | MACH_RCV_TIMEOUT, 0, size, bs_port, 0,
			    MACH_PORT_NULL) != KERN_SUCCESS) {
				free(big);
				return;
			}
			mach_msg_destroy(big);
			free(big);
			continue;
		}
		if (kr != KERN_SUCCESS) {
			return;
		}
		bs_handle(&in);
	}
}

/* --- shutting down ------------------------------------------------------------------ */

/* Start /etc/rc.shutdown, if there is one, and the timer that ends the wait for it. */
static void
start_rc_shutdown(void)
{
	if (access(RC_SHUTDOWN, R_OK) != 0) {
		return;
	}
	char *argv[] = { "sh", RC_SHUTDOWN, shutdown_how == RB_HALT ? "halt" : "reboot", NULL };
	pid_t pid = spawn_on_console("/", SHELL, argv, 0);
	if (pid <= 0) {
		return;
	}
	struct kevent ev;
	EV_SET(&ev, TIMER_RC_SHUTDOWN, EVFILT_TIMER, EV_ADD | EV_ONESHOT, NOTE_SECONDS, RC_SHUTDOWN_WAIT, NULL);
	if (kevent(kq, &ev, 1, NULL, 0, NULL) != 0) {
		say("cannot time %s: %s", RC_SHUTDOWN, strerror(errno));
		return;
	}
	rc_shutdown_pid = pid;
}

static void
shutdown_system(void)
{
	say("%s", shutdown_how == RB_HALT ? "halting" : "rebooting");
	kill(-1, SIGTERM);
	/* Two seconds for everything to quit, then SIGKILL. */
	for (int i = 0; i < 20; i++) {
		while (waitpid(-1, NULL, WNOHANG) > 0) {
		}
		if (kill(-1, 0) != 0 && errno == ESRCH) {
			break;
		}
		usleep(100000);
	}
	kill(-1, SIGKILL);
	while (waitpid(-1, NULL, WNOHANG) > 0) {
	}
	sync();
	reboot(shutdown_how);
	say("reboot: %s", strerror(errno));
	for (;;) {
		pause();
	}
}

int
main(void)
{
	if (getpid() != 1) {
		fprintf(stderr, "init: must be process 1\n");
		return 1;
	}
	open_console();
	setsid();

	/*
	 * Signals come in as kqueue events. kqueue records them although they
	 * are ignored, except SIGCHLD, which keeps its default action.
	 */
	kq = kqueue();
	int ignored[] = { SIGTERM, SIGUSR2, SIGHUP, SIGINT, SIGTSTP, SIGTTIN, SIGTTOU };
	for (size_t i = 0; i < sizeof(ignored) / sizeof(ignored[0]); i++) {
		signal(ignored[i], SIG_IGN);
	}
	struct kevent ev[3];
	EV_SET(&ev[0], SIGCHLD, EVFILT_SIGNAL, EV_ADD, 0, 0, NULL);
	EV_SET(&ev[1], SIGTERM, EVFILT_SIGNAL, EV_ADD, 0, 0, NULL);
	EV_SET(&ev[2], SIGUSR2, EVFILT_SIGNAL, EV_ADD, 0, 0, NULL);
	kevent(kq, ev, 3, NULL, 0, NULL);

	say("Blueberry Pie OS init starting");
	remount_root();
	setup_environment();
	chdir("/");
	umask(022);
	bs_setup();

	/* /etc/rc runs while init serves the bootstrap port; then the console login. */
	if (access(RC, R_OK) == 0) {
		char *argv[] = { "sh", RC, "autoboot", NULL };
		rc_pid = spawn_on_console("/", SHELL, argv, 0);
	}
	if (rc_pid <= 0) {
		rc_pid = 0;
		start_console();
	}

	/* Once a reboot or halt is asked for, serve on until /etc/rc.shutdown is done. */
	bool stopping = false;
	for (;;) {
		if (shutdown_how >= 0 && !stopping) {
			stopping = true;
			start_rc_shutdown();
		}
		if (stopping && rc_shutdown_pid == 0) {
			break;
		}
		struct kevent out[8];
		int n = kevent(kq, NULL, 0, out, 8, NULL);
		for (int i = 0; i < n; i++) {
			switch (out[i].filter) {
			case EVFILT_MACHPORT:
				if (out[i].ident == bs_notify) {
					bs_notify_drain();
				} else {
					bs_drain();
				}
				break;
			case EVFILT_SIGNAL:
				if (out[i].ident == SIGCHLD) {
					reap();
				} else if (shutdown_how < 0) {
					shutdown_how = out[i].ident == SIGUSR2 ? RB_HALT : RB_AUTOBOOT;
				}
				break;
			case EVFILT_TIMER:
				if (out[i].ident == TIMER_CONSOLE && console_pid == 0 && shutdown_how < 0) {
					start_console();
				} else if (out[i].ident == TIMER_RC_SHUTDOWN && rc_shutdown_pid != 0) {
					say("%s still running after %d seconds", RC_SHUTDOWN, RC_SHUTDOWN_WAIT);
					rc_shutdown_pid = 0;
				}
				break;
			}
		}
		/* A child may have exited before its SIGCHLD could be recorded. */
		reap();
	}
	shutdown_system();
	return 0;
}
