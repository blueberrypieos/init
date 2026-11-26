/*
 * SPDX-License-Identifier: BSD-2-Clause
 * Copyright (c) 2026 The Blueberry Pie OS Authors
 *
 * init: Blueberry Pie OS's process 1, installed as /sbin/launchd (the program
 * xnu starts). It is a small classic init that is also the bootstrap server:
 *
 *   - puts the console on standard input, output and error;
 *   - remounts the root filesystem read-write, unless it is a ZFS dataset
 *     whose readonly property is on (a sealed root);
 *   - runs ROOT_SETUP boot (ROOT_SETUP softboot after a soft reboot), if
 *     it is installed, and waits for it before /etc/rc;
 *   - serves the task bootstrap port that every process inherits: services
 *     check in, look up and register by name, and root can ask for a
 *     reboot or halt (the protocol of <pie/bootstrap.h>, which libxpc's
 *     bootstrap_* calls and reboot3() speak); only root may serve a
 *     system name, one that starts with SYSTEM_PREFIX or PIE_SYSTEM_PREFIX,
 *     or a host port name; a name is forgotten once its service's port
 *     dies, so that it can be checked in again and names made up at run
 *     time do not pile up;
 *   - makes the ports of the host port names at boot and sets them as the
 *     host's special ports, as launchd's HostSpecialPort does: auditd
 *     checks in com.apple.auditd, the kernel's audit control port, and
 *     kextd com.blueberrypieos.kextd, the port the kernel asks for kexts on;
 *   - runs /etc/rc (with /bin/sh), then keeps getty on the console,
 *     starting a new one when it exits, or a root shell without login;
 *     once /etc/rc exits, runs ROOT_SETUP rc STATUS boot|softboot;
 *   - on a reboot or halt, runs /etc/rc.shutdown (with /bin/sh) while it
 *     still serves the bootstrap port, for RC_SHUTDOWN_WAIT seconds at
 *     most, then stops every process;
 *   - on a soft reboot (reboot3() with RB2_USERREBOOT), runs
 *     /etc/rc.shutdown softreboot, stops every process, unmounts every
 *     file system but the root and /dev, switches the root to the ZFS
 *     dataset named in SOFTREBOOT_TARGET, if any, with pivot_root(2), and
 *     runs itself again as /sbin/launchd -softboot; if that fails, it
 *     reboots;
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
#include <sys/proc.h>
#include <sys/reboot.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/sysctl.h>
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
#define ROOT_SETUP       "/usr/libexec/pie-root-setup"
#define SOFTREBOOT_TARGET "/var/run/pie-softreboot"
#define NEXT_ROOT        "/System/Volumes/Next"
#define PREVIOUS_ROOT    "System/Volumes/Previous"
#define SELF             "/sbin/launchd"
#define RB2_USERREBOOT   0x2000000000000000ULL

struct zfs_mount_args {
	const char *fspec;
	int mflag;
	const char *optptr;
	int optlen;
	int struct_size;
};

int pivot_root(const char *new_rootfs_path_before, const char *old_rootfs_path_after);

static int shutdown_how = -1;         /* RB_* once a reboot or halt is asked for */
static bool soft_reboot;                /* the reboot asked for restarts user space only */
static bool softboot;                   /* started by a soft reboot */
static bool setup_failed;               /* ROOT_SETUP exited nonzero */
static pid_t setup_pid, rc_pid, console_pid, rc_shutdown_pid;
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
	} else if (strcmp(sfs.f_fstypename, "zfs") == 0) {
		struct zfs_mount_args args = { sfs.f_mntfromname, 0, NULL, 0, sizeof(args) };
		r = mount(sfs.f_fstypename, "/", (int)(sfs.f_flags & ~MNT_RDONLY) | MNT_UPDATE, &args);
		if (r != 0 && errno == EROFS) {
			say("the root %s is sealed: it stays read-only", sfs.f_mntfromname);
			return;
		}
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
static void start_console(void);

static void
start_rc(void)
{
	if (access(RC, R_OK) == 0) {
		char *argv[] = { "sh", RC, "autoboot", NULL };
		rc_pid = spawn_on_console("/", SHELL, argv, 0);
	}
	if (rc_pid <= 0) {
		rc_pid = 0;
		start_console();
	}
}

static void
start_setup(void)
{
	if (access(ROOT_SETUP, X_OK) == 0) {
		char *argv[] = { "pie-root-setup", softboot ? "softboot" : "boot", NULL };
		setup_pid = spawn_on_console("/", ROOT_SETUP, argv, 0);
	}
	if (setup_pid <= 0) {
		setup_pid = 0;
		start_rc();
	}
}

static void
rc_done(int status)
{
	char code[16];
	char *argv[] = { "pie-root-setup", "rc", code, softboot ? "softboot" : "boot", NULL };
	if (access(ROOT_SETUP, X_OK) != 0) {
		return;
	}
	snprintf(code, sizeof(code), "%d", setup_failed ? 1 : WIFEXITED(status) ? WEXITSTATUS(status) : 128);
	spawn_on_console("/", ROOT_SETUP, argv, 0);
}

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
		if (pid == setup_pid) {
			setup_pid = 0;
			if (status != 0) {
				setup_failed = true;
				say("%s exited with status %d", ROOT_SETUP,
				    WIFEXITED(status) ? WEXITSTATUS(status) : -1);
			}
			if (shutdown_how < 0) {
				start_rc();
			}
		} else if (pid == rc_pid) {
			rc_pid = 0;
			if (status != 0) {
				say("%s exited with status %d", RC,
				    WIFEXITED(status) ? WEXITSTATUS(status) : -1);
			}
			if (shutdown_how < 0) {
				start_console();
				rc_done(status);
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
#define PIE_SYSTEM_PREFIX "com.blueberrypieos.system."

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
	{ "com.blueberrypieos.kextd", HOST_KEXTD_PORT },
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
	return strncmp(name, SYSTEM_PREFIX, sizeof(SYSTEM_PREFIX) - 1) == 0 ||
	       strncmp(name, PIE_SYSTEM_PREFIX, sizeof(PIE_SYSTEM_PREFIX) - 1) == 0 || host_port_id(name) != 0;
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
			soft_reboot = shutdown_how == RB_AUTOBOOT && (req->arg & RB2_USERREBOOT) != 0;
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
	char *argv[] = { "sh", RC_SHUTDOWN,
		shutdown_how == RB_HALT ? "halt" : soft_reboot ? "softreboot" : "reboot", NULL };
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

static int
live_processes(bool report)
{
	int mib[3] = { CTL_KERN, KERN_PROC, KERN_PROC_ALL };
	size_t len = 0;
	if (sysctl(mib, 3, NULL, &len, NULL, 0) != 0) {
		return -1;
	}
	len += 16 * sizeof(struct kinfo_proc);
	struct kinfo_proc *kp = malloc(len);
	if (kp == NULL || sysctl(mib, 3, kp, &len, NULL, 0) != 0) {
		free(kp);
		return -1;
	}
	int n = 0;
	for (size_t i = 0; i < len / sizeof(*kp); i++) {
		struct extern_proc *p = &kp[i].kp_proc;
		if (p->p_pid <= 1 || p->p_stat == SZOMB || (p->p_flag & P_SYSTEM) != 0) {
			continue;
		}
		n++;
		if (report) {
			say("process %d (%s) outlived SIGKILL", p->p_pid, p->p_comm);
		}
	}
	free(kp);
	return n;
}

static bool
stop_processes(void)
{
	kill(-1, SIGTERM);
	/* Two seconds for everything to quit, then SIGKILL. */
	for (int i = 0; i < 20; i++) {
		while (waitpid(-1, NULL, WNOHANG) > 0) {
		}
		if (live_processes(false) == 0) {
			break;
		}
		usleep(100000);
	}
	kill(-1, SIGKILL);
	int left = -1;
	for (int i = 0; i < 50 && left != 0; i++) {
		while (waitpid(-1, NULL, WNOHANG) > 0) {
		}
		left = live_processes(false);
		if (left != 0) {
			usleep(100000);
		}
	}
	if (left != 0) {
		live_processes(true);
	}
	sync();
	return left == 0;
}

static bool
unmount_all(void)
{
	struct statfs *m;
	int n = getmntinfo(&m, MNT_NOWAIT);
	bool ok = true;
	if (n <= 0) {
		return false;
	}
	for (int i = n - 1; i >= 0; i--) {
		if (strcmp(m[i].f_mntonname, "/") == 0 || strcmp(m[i].f_fstypename, "devfs") == 0) {
			continue;
		}
		if (unmount(m[i].f_mntonname, 0) != 0 && unmount(m[i].f_mntonname, MNT_FORCE) != 0) {
			say("cannot unmount %s: %s", m[i].f_mntonname, strerror(errno));
			ok = false;
		}
	}
	return ok;
}

static void
soft_restart(void)
{
	char target[MAXPATHLEN] = "";
	FILE *f = fopen(SOFTREBOOT_TARGET, "r");
	if (f != NULL) {
		if (fgets(target, sizeof(target), f) == NULL) {
			target[0] = '\0';
		}
		target[strcspn(target, "\n")] = '\0';
		fclose(f);
		unlink(SOFTREBOOT_TARGET);
	}
	say("restarting user space%s%s", target[0] != '\0' ? " on " : "", target);
	if (!stop_processes()) {
		return;
	}
	if (!unmount_all()) {
		return;
	}
	struct statfs root;
	if (target[0] != '\0' && (statfs("/", &root) != 0 || strcmp(root.f_mntfromname, target) != 0)) {
		struct zfs_mount_args args = { target, 0, NULL, 0, sizeof(args) };
		if (mount("zfs", NEXT_ROOT, MNT_RDONLY, &args) != 0) {
			say("cannot mount %s on %s: %s", target, NEXT_ROOT, strerror(errno));
			return;
		}
		if (pivot_root(NEXT_ROOT, PREVIOUS_ROOT) != 0) {
			say("cannot switch the root to %s: %s", target, strerror(errno));
			unmount(NEXT_ROOT, 0);
			return;
		}
	}
	chdir("/");
	if (usrctl(0) != 0) {
		say("usrctl: %s", strerror(errno));
		return;
	}
	char *argv[] = { "launchd", "-softboot", NULL };
	execv(SELF, argv);
	say("cannot run %s: %s", SELF, strerror(errno));
}

static void
shutdown_system(void)
{
	open_console();
	if (soft_reboot) {
		soft_restart();
		shutdown_how = RB_AUTOBOOT;
	}
	say("%s", shutdown_how == RB_HALT ? "halting" : "rebooting");
	stop_processes();
	reboot(shutdown_how);
	say("reboot: %s", strerror(errno));
	for (;;) {
		pause();
	}
}

int
main(int argc, char *argv[])
{
	if (getpid() != 1) {
		fprintf(stderr, "init: must be process 1\n");
		return 1;
	}
	softboot = argc > 1 && strcmp(argv[1], "-softboot") == 0;
	open_console();
	setsid();

	/*
	 * Signals come in as kqueue events. kqueue records them although they
	 * are ignored, except SIGCHLD, which keeps its default action.
	 */
	kq = kqueue();
	fcntl(kq, F_SETFD, FD_CLOEXEC);
	int ignored[] = { SIGTERM, SIGUSR2, SIGHUP, SIGINT, SIGTSTP, SIGTTIN, SIGTTOU };
	for (size_t i = 0; i < sizeof(ignored) / sizeof(ignored[0]); i++) {
		signal(ignored[i], SIG_IGN);
	}
	struct kevent ev[3];
	EV_SET(&ev[0], SIGCHLD, EVFILT_SIGNAL, EV_ADD, 0, 0, NULL);
	EV_SET(&ev[1], SIGTERM, EVFILT_SIGNAL, EV_ADD, 0, 0, NULL);
	EV_SET(&ev[2], SIGUSR2, EVFILT_SIGNAL, EV_ADD, 0, 0, NULL);
	kevent(kq, ev, 3, NULL, 0, NULL);

	say("Blueberry Pie OS init starting%s", softboot ? " after a soft reboot" : "");
	if (softboot && unmount("/" PREVIOUS_ROOT, 0) != 0 && errno != EINVAL && errno != ENOENT) {
		say("cannot unmount /%s: %s", PREVIOUS_ROOT, strerror(errno));
	}
	remount_root();
	setup_environment();
	chdir("/");
	umask(022);
	bs_setup();

	/* The root setup, then /etc/rc, run while init serves the bootstrap port; then the console login. */
	start_setup();

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
