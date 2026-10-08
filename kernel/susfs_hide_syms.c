// SPDX-License-Identifier: GPL-2.0
/*
 * susfs_hide_syms.c - hide ksu/susfs symbols from /proc/kallsyms (SUSFS HIDE_KSU_SUSFS_SYMBOLS feature), LKM port.
 * Upstream patches kernel/kallsyms.c s_show() to skip symbols whose name starts with ksu_/__ksu_/susfs_/ksud/...  s_show is
 * static but sits in the kallsyms_op.show seq_operations pointer, so LTO keeps an out-of-line copy and a kprobe can hang
 * on it.  A matching prefix returns early (regs->regs[0] = 0, regs->pc = x30), so the line is never printed - covering
 * BOTH core-kernel and module symbols, since the whole body is skipped before it branches on module_name.  On by default
 * like upstream (a build-time CONFIG there, no runtime toggle).
 */
#include <linux/module.h>
#include <linux/version.h>	/* LINUX_VERSION_CODE: the kallsym_iter mirror below is version-gated */
#include <linux/kprobes.h>
#include <linux/seq_file.h>
#include <linux/kallsyms.h>
#include <linux/string.h>
#include <linux/proc_fs.h>	/* the runtime control node */
#include <linux/cred.h>		/* current_uid() */
#include <linux/slab.h>		/* kvmalloc()/kvfree() on 6.1+ */
#include <linux/mm.h>		/* kvmalloc()/kvfree() on 5.10-5.15 */
#include "susfs_log.h"
#include "susfs.h"		/* sus_path_add_self_hidden / sus_path_del_path */
#include "symbol_resolver.h"	/* find_kernel_symbol_exact (kallsyms_op) */

/* ---- hide_modules: filter other kernel modules out of /proc/modules ----
 * /proc/modules is world-readable (0444) and lists every loaded module, so a checker that greps it sees the whole set
 * including the module doing the hiding.  The feature keeps a list of module NAMES and removes them from: (1)
 * /proc/modules - the m_show() line, for EVERY reader, root included, since a checker may well run as root and this
 * listing is what it compares against; (2) /sys/module/<name> - registered in sus_path with self_protect, so
 * stat/open/readdir answer ENOENT for non-root callers while root keeps access (that is where a module's parameters
 * live) - the one asymmetry to know; (3) /proc/kallsyms lines whose module_name matches, also for every reader.
 * Two frontends over one list: /proc/susfs_hide_modules (`add <name> | del <name> | clear | <name> [<name> ...]`, root
 * only, ENOENT for everyone else) and .../parameters/hide_modules (same commands, settable at insmod).  Both follow the
 * house pattern of the control nodes: 0777 so DAC passes and sus_path's hidden set is the only answer (ENOENT,
 * indistinguishable from "no such file"), plus a uid check in open() AND write() so a passed-on fd is not a way in.  The
 * default list holds just this module, because a built-in SUSFS has no module entry; `clear` is the debugging mode.
 * Not a new CMD_SUSFS_* command: that id space is shared with KernelSU's own copy of SUSFS and a new id there is a
 * compatibility risk that buys nothing. */
#define HIDE_MODULES_MAX 16
#define HIDE_MODULES_CMDLINE (HIDE_MODULES_MAX * (MODULE_NAME_LEN + 1) + 96)

static char hide_modules[HIDE_MODULES_MAX][MODULE_NAME_LEN];
static char hide_modules_applied[HIDE_MODULES_MAX][MODULE_NAME_LEN];	/* sysfs rules live */
static int n_hide_modules;
static int n_hide_modules_applied;
static DEFINE_SPINLOCK(hide_modules_lock);

static atomic_t n_modlines_skipped = ATOMIC_INIT(0);	/* /proc/modules lines removed */
static atomic_t n_kallsyms_mod_skipped = ATOMIC_INIT(0);	/* kallsyms lines of those modules */
static atomic_t n_sysfs_rules_added = ATOMIC_INIT(0);
static atomic_t n_sysfs_rules_failed = ATOMIC_INIT(0);

/* Interrupt/kprobe safe: no allocation, no sleeping - callers are probe handlers. */
static bool hide_module_name_match(const char *name)
{
	unsigned long flags;
	bool hit = false;
	int i;

	if (!name || !name[0])
		return false;

	spin_lock_irqsave(&hide_modules_lock, flags);
	for (i = 0; i < n_hide_modules; i++) {
		if (!strcmp(hide_modules[i], name)) {
			hit = true;
			break;
		}
	}
	spin_unlock_irqrestore(&hide_modules_lock, flags);
	return hit;
}

/* No internal caller since the feature list stopped advertising hide_modules (susfs_supercall.c);
 * kept because hide_modules is still a /proc-visible feature. */
bool susfs_hide_modules_active(void)
{
	return n_hide_modules > 0;
}

/* Reconcile the /sys/module/<name> rules with the list: one rule per listed name.  Process context. */
static void hide_modules_sync_sysfs(void)
{
	char path[64];
	int i;

	/* sus_path_del_path() is a no-op for a name that was never registered. */
	for (i = 0; i < n_hide_modules_applied; i++) {
		snprintf(path, sizeof(path), "/sys/module/%s", hide_modules_applied[i]);
		sus_path_del_path(path);
	}
	n_hide_modules_applied = 0;

	for (i = 0; i < n_hide_modules; i++) {
		int rc;

		snprintf(path, sizeof(path), "/sys/module/%s", hide_modules[i]);
		rc = sus_path_add_self_hidden(path);
		if (rc) {
			/* Not fatal: the /proc/modules line is filtered with or without a sysfs directory (-ENOENT: not loaded yet). */
			atomic_inc(&n_sysfs_rules_failed);
			SUSFS_LOGI("hide_modules: %s: no sus_path rule (%d%s)\n", path, rc,
				rc == -ENOENT ? " - not loaded, so its sysfs directory does not exist yet" : "");
			continue;
		}
		strscpy(hide_modules_applied[n_hide_modules_applied++],
			hide_modules[i], MODULE_NAME_LEN);
		atomic_inc(&n_sysfs_rules_added);
	}
}

/* Parse @val into @dst and return the count, or a negative errno.  Separators are spaces, commas and tabs, so both the
 * insmod form (hide_modules=a,b) and the /proc form (a b) work.  @buf is 1136 bytes and the caller below is checked against
 * the same 2048-byte frame limit, so it is allocated rather than kept on the stack (see hide_modules_command). */
static int hide_modules_parse(const char *val, char dst[][MODULE_NAME_LEN], int max)
{
	char *buf;
	const char *p;
	int n = 0;
	int rc;

	buf = kvmalloc(HIDE_MODULES_CMDLINE, GFP_KERNEL);
	if (!buf)
		return -ENOMEM;

	strscpy(buf, val, HIDE_MODULES_CMDLINE);
	p = buf;
	while (*p) {
		char *tok = (char *)p;
		int len;

		while (*p == ' ' || *p == ',' || *p == '\t' || *p == '\n' || *p == '\r')
			p++;
		if (!*p)
			break;
		tok = (char *)p;
		while (*p && *p != ' ' && *p != ',' && *p != '\t' && *p != '\n' && *p != '\r')
			p++;
		len = (int)(p - tok);
		if (len <= 0)
			continue;
		if (len >= MODULE_NAME_LEN) {
			rc = -ENAMETOOLONG;	/* longer than any module name */
			goto out;
		}
		if (n >= max) {
			rc = -ENOSPC;
			goto out;
		}
		memcpy(dst[n], tok, len);
		dst[n][len] = '\0';
		n++;
	}
	rc = n;
out:
	kvfree(buf);
	return rc;
}

static void hide_modules_commit(char dst[][MODULE_NAME_LEN], int n)
{
	unsigned long flags;

	spin_lock_irqsave(&hide_modules_lock, flags);
	memset(hide_modules, 0, sizeof(hide_modules));
	memcpy(hide_modules, dst, (size_t)n * MODULE_NAME_LEN);
	n_hide_modules = n;
	spin_unlock_irqrestore(&hide_modules_lock, flags);
}

/* One implementation for both frontends.  Commands: `clear`, `add <name>`, `del <name>`, `set <name> [<name>...]`.
 *
 * @bare_list is the one difference: insmod hands the parameter a bare value (`hide_modules=a,b`), so its setter accepts a
 * command-less list; the /proc node does NOT - a typo there would otherwise silently *replace* the list with whatever was
 * typed (measured on the first device test, where a bogus command discarded the list and the next read showed a name
 * nobody meant).
 *
 * The two staging buffers (1136 + 1024 bytes) are heap-allocated: as locals they made this function's frame 3024 bytes once
 * the inliner folded hide_modules_parse() (and its own 1136-byte buffer) into it, which the 5.10/5.15 builds reported every
 * build - "ld.lld: warning: stack frame size (3024) exceeds limit (2048) in function 'hide_modules_command'", and
 * 5.15/android14-5.15 as "susfs_hide_syms.c:197:0: stack frame size (3024) exceeds limit (2048)".  6.x turns that warning
 * into an error.  Both callers are proc/module_param setters - process context - so GFP_KERNEL is fine. */
static int hide_modules_command(const char *val, bool bare_list)
{
	char *cmd;
	char (*staged)[MODULE_NAME_LEN];
	const char *arg;
	int i, n;
	int rc = 0;

	cmd = kvmalloc(HIDE_MODULES_CMDLINE, GFP_KERNEL);
	staged = kvmalloc_array(HIDE_MODULES_MAX, MODULE_NAME_LEN, GFP_KERNEL);
	if (!cmd || !staged) {
		kvfree(cmd);
		kvfree(staged);
		return -ENOMEM;
	}

	strscpy(cmd, val, HIDE_MODULES_CMDLINE);
	for (i = (int)strlen(cmd) - 1; i >= 0 && (cmd[i] == '\n' || cmd[i] == '\r' || cmd[i] == ' '); i--)
		cmd[i] = '\0';

	if (!strcmp(cmd, "clear")) {
		hide_modules_commit(staged, 0);
		hide_modules_sync_sysfs();
		SUSFS_LOGI("hide_modules: list cleared (no module is filtered)\n");
		goto out;
	}

	if (!strncmp(cmd, "set ", 4)) {
		n = hide_modules_parse(cmd + 4, staged, HIDE_MODULES_MAX);
		if (n < 0) {
			rc = n;
			goto out;
		}
		hide_modules_commit(staged, n);
		hide_modules_sync_sysfs();
		SUSFS_LOGI("hide_modules: list set to %d name(s)\n", n);
		goto out;
	}

	if (!strncmp(cmd, "add ", 4) || !strncmp(cmd, "del ", 4)) {
		bool adding = (cmd[0] == 'a');

		arg = cmd + 4;
		while (*arg == ' ')
			arg++;
		if (!*arg || strlen(arg) >= MODULE_NAME_LEN) {
			rc = -EINVAL;
			goto out;
		}

		spin_lock(&hide_modules_lock);
		n = n_hide_modules;
		if (n > HIDE_MODULES_MAX)
			n = HIDE_MODULES_MAX;
		memcpy(staged, hide_modules, (size_t)n * MODULE_NAME_LEN);
		spin_unlock(&hide_modules_lock);

		/* `found` is kept separate from `i` on purpose: after a del the index and the new count coincide whenever the
		 * removed entry was the last one, and reusing `i` for both questions answered -ENOENT for a name that was right
		 * there (measured: `del <last entry>` always failed). */
		{
			bool found = false;

			for (i = 0; i < n; i++) {
				if (strcmp(staged[i], arg))
					continue;
				found = true;
				if (adding)
					goto out;	/* already listed */
				memmove(&staged[i], &staged[i + 1],
					(size_t)(n - i - 1) * MODULE_NAME_LEN);
				n--;
				break;
			}
			if (adding) {
				if (found)
					goto out;
				if (n >= HIDE_MODULES_MAX) {
					rc = -ENOSPC;
					goto out;
				}
				strscpy(staged[n], arg, MODULE_NAME_LEN);
				n++;
			} else if (!found) {
				rc = -ENOENT;		/* not listed */
				goto out;
			}
		}
		hide_modules_commit(staged, n);
		hide_modules_sync_sysfs();
		SUSFS_LOGI("hide_modules: %s %s -> %d name(s) filtered\n",
			adding ? "add" : "del", arg, n);
		goto out;
	}

	if (!bare_list) {
		rc = -EINVAL;
		goto out;
	}

	n = hide_modules_parse(cmd, staged, HIDE_MODULES_MAX);
	if (n < 0) {
		rc = n;
		goto out;
	}
	hide_modules_commit(staged, n);
	hide_modules_sync_sysfs();
	SUSFS_LOGI("hide_modules: list set to %d name(s)\n", n);

out:
	kvfree(staged);
	kvfree(cmd);
	return rc;
}

static int hide_modules_format_unlocked(char *buf, size_t size)
{
	int n = 0;
	int i;

	n += scnprintf(buf + n, size - n,
		"hide_modules: %d/%d name(s), /sys/module rules=%d (failed=%d), "
		"/proc/modules lines removed=%d, kallsyms lines removed=%d\n",
		n_hide_modules, HIDE_MODULES_MAX, n_hide_modules_applied,
		atomic_read(&n_sysfs_rules_failed),
		atomic_read(&n_modlines_skipped), atomic_read(&n_kallsyms_mod_skipped));
	n += scnprintf(buf + n, size - n, "names:");
	for (i = 0; i < n_hide_modules && n < (int)size - 64; i++)
		n += scnprintf(buf + n, size - n, " %s", hide_modules[i]);
	n += scnprintf(buf + n, size - n, "\n");
	return n;
}

/* The writer publishes under hide_modules_lock (hide_modules_commit() memsets the whole table
 * and then memcpys the new one), so the reader has to hold the same lock: without it a reader
 * could run between those two steps and print the name count of the new list with every name
 * still zeroed.  Formatting under the lock is safe - scnprintf does not sleep - and it is what
 * hide_module_name_match() already does on the kprobe side. */
static int hide_modules_format(char *buf, size_t size)
{
	unsigned long flags;
	int n;

	spin_lock_irqsave(&hide_modules_lock, flags);
	n = hide_modules_format_unlocked(buf, size);
	spin_unlock_irqrestore(&hide_modules_lock, flags);
	return n;
}

/* ---- insmod parameters must not touch the guard-protected side ---------------------------------
 * module_param_cb()'s setter runs during load_module()'s parse_args(), i.e. BEFORE susfs_init() has
 * reached susfs_imports_guard() and before any layer is up.  Applying `hide_modules=<value>` there
 * reached hide_modules_sync_sysfs() -> sus_path_add_self_hidden() -> kern_path()/ihold() and
 * sus_path_hooks_arm(), and even reading the table for `add`/`del` takes hide_modules_lock - all of
 * them imports the guard's table covers (imports_guard.c), so a loader that left one of them at zero
 * jumped to address 0 before anything could refuse the load.  (The guard's table is not the whole
 * import set: ordinary exports such as strscpy/kvmalloc are the loader's and the build-time System.map
 * gate's business, so the validation below may use them.)
 *
 * The setter therefore only validates the shape and caches the raw value - the command form is kept,
 * because the parameter documents the same commands as the /proc node - and susfs_hide_syms_init()
 * applies it with the very same entry point (hide_modules_command()) once the guard has passed.
 * hide_syms_ready marks the point after which the setter applies live, and hide_syms_param_lock keeps
 * the two orders from interleaving: without it a sysfs write landing between "ready = true" and the
 * cached apply could be overwritten by the older cached value (hide_modules is a commit, not an
 * append).
 *
 * One entry of that table is still reached from here on purpose: hide_syms_param_lock is taken in
 * parse_args(), and mutex_lock/mutex_unlock are in that table as well - so a loader that left those two
 * at zero would jump to address 0 before susfs_init() could refuse the load.  It is not removable by a
 * local change: the mutex is what orders "cache the value" against "apply the cached value", and the
 * other mutual-exclusion primitives available here (_raw_spin_lock*, __rcu_read_*) are in that table
 * too.  Closing it needs a lock-free publication of the cached value (store, then re-check the ready
 * flag and apply live), which is a change of its own. */
static char hide_modules_pending_val[HIDE_MODULES_CMDLINE];
static bool hide_modules_pending_given;
static bool hide_syms_ready;
static DEFINE_MUTEX(hide_syms_param_lock);

/* Validation only, and through the same parser the command uses, so the limits and the error codes
 * cannot drift.  No table, no lock, no VFS - safe to call from parse_args(). */
static int hide_modules_list_check(const char *list)
{
	char (*dst)[MODULE_NAME_LEN];
	int rc;

	dst = kvmalloc_array(HIDE_MODULES_MAX, MODULE_NAME_LEN, GFP_KERNEL);
	if (!dst)
		return -ENOMEM;
	rc = hide_modules_parse(list, dst, HIDE_MODULES_MAX);
	kvfree(dst);
	return rc < 0 ? rc : 0;
}

/* The grammar hide_modules_command() accepts, checked without running it.  @val is modified in place
 * (trailing whitespace trimmed), which is why the caller hands over its own copy. */
static int hide_modules_check(char *val)
{
	const char *arg;
	size_t i;

	for (i = strlen(val); i > 0 && (val[i - 1] == '\n' || val[i - 1] == '\r' || val[i - 1] == ' '); i--)
		val[i - 1] = '\0';

	if (!val[0] || !strcmp(val, "clear"))
		return 0;
	if (!strncmp(val, "set ", 4))
		return hide_modules_list_check(val + 4);
	if (!strncmp(val, "add ", 4) || !strncmp(val, "del ", 4)) {
		arg = val + 4;
		while (*arg == ' ')
			arg++;
		if (!*arg || strlen(arg) >= MODULE_NAME_LEN)
			return -EINVAL;
		/* parse_args runs before the table has a single name in it, so `del` here could only fail later
		 * (-ENOENT, "not listed").  Reject it at the insmod instead - that is what it used to do. */
		if (val[0] == 'd')
			return -EINVAL;
		return 0;
	}
	return hide_modules_list_check(val);
}

/* ---- the two frontends ---- */

static int hide_modules_param_set(const char *val, const struct kernel_param *kp)
{
	int rc;

	mutex_lock(&hide_syms_param_lock);
	if (hide_syms_ready) {
		mutex_unlock(&hide_syms_param_lock);
		return hide_modules_command(val, true);	/* module is up: apply live */
	}

	/* parse_args(): validate the shape and cache the raw value - the command form is part of the
	 * parameter's contract, so it is applied later with the same entry point (see
	 * hide_modules_pending_val).  A typo still fails the insmod here.  Validate the value itself,
	 * not a copy that was already truncated to the cache size. */
	if (strlen(val) >= sizeof(hide_modules_pending_val)) {
		mutex_unlock(&hide_syms_param_lock);
		return -EINVAL;
	}
	strscpy(hide_modules_pending_val, val, sizeof(hide_modules_pending_val));
	rc = hide_modules_check(hide_modules_pending_val);
	if (!rc)
		hide_modules_pending_given = true;
	mutex_unlock(&hide_syms_param_lock);
	return rc;
}

static int hide_modules_param_get(char *buf, const struct kernel_param *kp)
{
	return hide_modules_format(buf, PAGE_SIZE);
}

static const struct kernel_param_ops hide_modules_ops = {
	.get = hide_modules_param_get,
	.set = hide_modules_param_set,
};
/* 0600: root reads and writes it, and the whole directory is inside the one the hide_modules feature hides from everyone. */
module_param_cb(hide_modules, &hide_modules_ops, NULL, 0600);

static int hide_modules_proc_show(struct seq_file *m, void *v)
{
	char buf[512];

	hide_modules_format(buf, sizeof(buf));
	seq_puts(m, buf);
	return 0;
}

static int hide_modules_proc_open(struct inode *inode, struct file *file)
{
	/* 0777 node + this check, exactly like the other control nodes: a restrictive mode would answer EACCES (which
	 * advertises that the node exists) before sus_path could answer ENOENT. */
	if (current_uid().val != 0)
		return -ENOENT;
	return single_open(file, hide_modules_proc_show, NULL);
}

static ssize_t hide_modules_proc_write(struct file *file, const char __user *buf,
				       size_t len, loff_t *off)
{
	char cmd[HIDE_MODULES_CMDLINE];
	int rc;

	/* Same reason as the open check: an fd opened before the process dropped privileges must not become a way in. */
	if (current_uid().val != 0)
		return -ENOENT;
	if (len == 0)
		return 0;
	if (len >= sizeof(cmd))
		return -EINVAL;
	if (copy_from_user(cmd, buf, len))
		return -EFAULT;
	cmd[len] = '\0';

	/* The node takes commands only: a typo must not silently replace the list. */
	rc = hide_modules_command(cmd, false);
	if (rc)
		return rc;
	return len;
}

static const struct proc_ops hide_modules_proc_ops = {
	.proc_open = hide_modules_proc_open,
	.proc_read = seq_read,
	.proc_write = hide_modules_proc_write,
	.proc_lseek = seq_lseek,
	.proc_release = single_release,
};

static struct proc_dir_entry *hide_modules_entry;

/* Local mirror of kernel/kallsyms.c struct kallsym_iter; only the name field matters here.
 *
 * It is a MIRROR, so the compiler cannot check it against the kernel's own struct, and the layout
 * is not KMI-frozen across the versions this module builds against: v6.5 removed `pos_arch_end`
 * (measured against upstream: v5.10/v5.15/v6.1 have it, v6.6 does not).  Getting this wrong
 * shifts `name`/`module_name` by 8 bytes, which makes every prefix and module-name test miss
 * while all the counters still report "armed" - a silent no-op, not a crash.  Hence the gate
 * below for the drift that is known, and the plausibility check in hide_syms_s_show_pre() for
 * the drift that is not. */
struct kallsym_iter_local {
	loff_t pos;
#if LINUX_VERSION_CODE < KERNEL_VERSION(6, 5, 0)
	loff_t pos_arch_end;		/* gone in v6.5 */
#endif
	loff_t pos_mod_end;
	loff_t pos_ftrace_mod_end;
	loff_t pos_bpf_end;
	unsigned long value;
	unsigned int nameoff;
	char type;
	char name[KSYM_NAME_LEN];
	char module_name[MODULE_NAME_LEN];
	int exported;
	int show_value;
};

/* prefixes to hide (matches upstream's list) */
static const char *const hide_prefixes[] = {
	"ksu_", "__ksu_", "susfs_", "susfs_guard_lkm", "ksud",
	"is_ksu_", "is_manager_", "escape_to_", "setup_selinux",
	"track_throne", "on_post_fs_data", "try_umount", "kernelsu",
	"__initcall__kmod_kernelsu", "apply_kernelsu", "handle_sepolicy",
	"getenforce", "setenforce", "is_zygote",
};

static bool name_should_hide(const char *name)
{
	int i;

	for (i = 0; i < ARRAY_SIZE(hide_prefixes); i++)
		if (!strncmp(name, hide_prefixes[i], strlen(hide_prefixes[i])))
			return true;

	/* Substring form for the names whose prefix differs from the list above.  Measured: with the prefix rules alone a
	 * 257 -> 7 sweep left anon_ksu_fops, anon_ksu_ioctl(.cfi_jt), anon_ksu_release(.cfi_jt), setup_ksu_cred and
	 * is_task_ksu_domain visible - each a plain "KernelSU is loaded here" tell in /proc/kallsyms. */
	if (strstr(name, "ksu") || strstr(name, "susfs"))
		return true;

	return false;
}

static atomic_t hide_hit_count = ATOMIC_INIT(0);
static atomic_t hide_enter_count = ATOMIC_INIT(0);
static atomic_t hide_layout_bad = ATOMIC_INIT(0);

/* Is this really a kernel struct kallsym_iter?  Two facts are always true of one: kallsyms
 * fills `type` from its own alphabet, and `name` is NUL-terminated within the field.  The check
 * exists because this kprobe is registered BY NAME and `s_show` is not unique in a kernel that
 * has kernel/kallsyms.c's and kernel/trace/trace.c's (and mm/vmalloc.c's); if it lands on the
 * wrong one, m->private is some other object and walking it with strncmp and strstr reads
 * whatever is there.  With this gate the string walk below is bounded either way, and a
 * mismatch is counted and reported instead of silently mis-hiding. */
static bool hide_syms_iter_plausible(const struct kallsym_iter_local *it)
{
	if (!it->type || !strchr("aAbBdDgGijNnRrSsTtUuVvWw", it->type))
		return false;
	if (strnlen(it->name, sizeof(it->name)) >= sizeof(it->name))
		return false;
	/* Empty for a core-kernel symbol, a short module name otherwise - never unterminated. */
	return strnlen(it->module_name, sizeof(it->module_name)) < sizeof(it->module_name);
}

/* s_show(m, p): m is arg #1 (regs->regs[0]) */
static int hide_syms_s_show_pre(struct kprobe *kp, struct pt_regs *regs)
{
	struct seq_file *m = (struct seq_file *)regs->regs[0];
	struct kallsym_iter_local *iter;

	atomic_inc(&hide_enter_count);
	if (!m || !m->private)
		return 0;
	iter = (struct kallsym_iter_local *)m->private;
	if (!hide_syms_iter_plausible(iter)) {
		if (atomic_inc_return(&hide_layout_bad) == 1)
			pr_err("susfs_hide_syms: m->private does not look like struct kallsym_iter - the kprobe is on another s_show or the mirror drifted; not touching it (symbol hiding is NOT active)\n");
		return 0;
	}
	if (!iter->name[0])
		return 0;

	/* Two different features, counted apart: the prefix list is upstream's HIDE_KSU_SUSFS_SYMBOLS (KernelSU's names),
	 * while the module_name test is hide_modules, which filters the lines of whichever modules the operator listed -
	 * module symbols carry their own spelling (e.g. __kstrtab_foo) with the module's name in module_name. */
	if (name_should_hide(iter->name)) {
		atomic_inc(&hide_hit_count);
		regs->regs[0] = 0;              /* s_show returns 0 */
		regs->pc = regs->regs[30];      /* skip the line */
		return 1;
	}
	if (iter->module_name[0] && hide_module_name_match(iter->module_name)) {
		atomic_inc(&n_kallsyms_mod_skipped);
		regs->regs[0] = 0;
		regs->pc = regs->regs[30];
		return 1;
	}
	return 0;
}

/* Registered by name, which is what was measured to work: with this in place `grep -cE 'susfs_|ksu_' /proc/kallsyms` goes 257
 * -> 0.  An audit pointed out that this tree has three different `s_show` functions (kernel/kallsyms.c, kernel/trace/trace.c,
 * mm/vmalloc.c) and that name-based registration gets whichever kallsyms lists first - a real hazard, since the handler reads
 * m->private as struct kallsym_iter *.  Taking the address out of the kallsyms_op table instead and registering with .addr
 * CRASHED the device on the first read of /proc/kallsyms, so the table's .show is not the address a kprobe can be hung on
 * (most likely the arm64 CFI jump-table thunk, which a table's function pointer holds under this config).  So: keep the
 * working registration, and log both addresses so a mismatch is visible. */
static struct kprobe kp_s_show = {
	.symbol_name = "s_show",
	.pre_handler = hide_syms_s_show_pre,
};

/* /proc/modules is 0444 - any app can read it - and nothing in a built-in SUSFS is listed there.  Our own line is printed
 * by m_show(m, p) with p = &module->list; answering success without emitting anything leaves the listing exactly as it
 * would be without the module.  struct module's layout is what this module was built against (RANDSTRUCT is off here). */
static int hide_syms_m_show_pre(struct kprobe *kp, struct pt_regs *regs)
{
	struct module *mod;
	void *p = (void *)regs_get_kernel_argument(regs, 1);

	if (!p)
		return 0;

	/* Same recovery the kernel's own m_show() does: the iterator hands over &module->list, so the module is one offset away. */
	mod = (struct module *)((char *)p - offsetof(struct module, list));
	if (!hide_module_name_match(mod->name))
		return 0;

	atomic_inc(&n_modlines_skipped);
	regs_set_return_value(regs, 0);		/* no output for this entry */
	regs->pc = regs->regs[30];
	return 1;
}

static struct kprobe kp_m_show = {
	.symbol_name = "m_show",
	.pre_handler = hide_syms_m_show_pre,
};

static bool m_show_registered;

/* Read-only comparison target: the function kallsyms itself calls. */
static unsigned long hide_syms_table_show(void)
{
	const struct seq_operations *op;
	unsigned long addr = find_kernel_symbol_exact("kallsyms_op");

	if (!addr)
		return 0;
	op = (const struct seq_operations *)addr;
	return (unsigned long)op->show;
}

static bool hide_registered;

int susfs_hide_syms_init(void)
{
	int rc;
	unsigned long table_show;

	/* Apply what the insmod parameter cached (see hide_modules_pending_val) FIRST, and before the
	 * kprobe registrations below: those can fail without failing the load (this layer is non-fatal in
	 * the layer table), and the operator's list must not be lost because of an unrelated probe.  The
	 * import guard has passed by now, and sus_path is up (this layer is last), which is what the sysfs
	 * rules need.  From here on the setter applies live. */
	mutex_lock(&hide_syms_param_lock);
	hide_syms_ready = true;
	if (hide_modules_pending_given) {
		rc = hide_modules_command(hide_modules_pending_val, true);
		mutex_unlock(&hide_syms_param_lock);
		if (rc) {
			pr_err("susfs_hide_syms: applying hide_modules=\"%s\" from insmod failed %d\n",
					hide_modules_pending_val, rc);
			return rc;
		}
	} else {
		mutex_unlock(&hide_syms_param_lock);
	}

	rc = register_kprobe(&kp_s_show);
	if (rc) {
		pr_warn("susfs_hide_syms: register_kprobe(s_show) failed %d\n", rc);
		return rc;
	}
	hide_registered = true;

	table_show = hide_syms_table_show();
	/* The two addresses differ by design: a function pointer inside a table holds the CFI jump-table thunk
	 * (bti c ; b func), while the kprobe lands on the function itself.  The check that matters is the one on device -
	 * /proc/kallsyms going from 257 ksu_/susfs_ matches to none - and that is what the line is for. */
	SUSFS_LOGI("susfs_hide_syms: armed at %px (kallsyms_op.show=%px%s)\n",
		(void *)kp_s_show.addr, (void *)table_show,
		(table_show && (unsigned long)kp_s_show.addr == table_show) ?
		" - same address" : " - different address (expected: table holds the CFI thunk)");

	/* Separate probe, separate failure: hiding symbol names and hiding module entries are independent. */
	rc = register_kprobe(&kp_m_show);
	if (rc)
		pr_warn("susfs_hide_syms: register_kprobe(m_show) failed %d - /proc/modules keeps listing the modules in hide_modules\n",
			rc);
	else
		m_show_registered = true;

	/* hide_modules starts with just this module in its list: a built-in SUSFS has no module entry, so leaving ours visible
	 * would be a trace upstream does not have.  The sysfs rule can only be registered now, because sus_path is up (this
	 * layer is last in the init table).
	 *
	 * A list that is already populated came from the insmod parameter (applied at the top of this function):
	 * module_param_cb()'s setter runs during load_module()'s parse_args(), i.e. before module_init, so the operator's
	 * names are the whole point of the parameter.  Append our own name to whatever is there instead, and only seed the
	 * default when nothing supplied a list. */
	if (n_hide_modules == 0)
		hide_modules_command(SUSFS_LKM_MODULE_NAME, true);
	else
		hide_modules_command("add " SUSFS_LKM_MODULE_NAME, false);
	hide_modules_sync_sysfs();

	/* The runtime control node: created only when the LSM layer that hides it is installed, so an unprotected
	 * world-writable node cannot exist (same shape as the other control nodes - see susfs_control_node_allowed()). */
	if (susfs_control_node_allowed()) {
		hide_modules_entry = proc_create("susfs_hide_modules", 0777, NULL,
						 &hide_modules_proc_ops);
		if (!hide_modules_entry)
			pr_warn("susfs_hide_syms: proc_create(susfs_hide_modules) failed - runtime control unavailable, use the hide_modules parameter\n");
	} else {
		SUSFS_LOGI("susfs_hide_syms: /proc/susfs_hide_modules not created (expose_proc=%d lsm=%d)\n",
			(int)susfs_expose_proc, (int)sus_path_lsm_active());
	}

	return 0;
}

bool susfs_hide_syms_active(void)
{
	return hide_registered;
}

bool susfs_hide_modules_node_ready(void)
{
	return hide_modules_entry != NULL;
}

void susfs_hide_syms_exit(void)
{
	if (hide_modules_entry) {
		proc_remove(hide_modules_entry);
		hide_modules_entry = NULL;
	}
	if (m_show_registered) {
		unregister_kprobe(&kp_m_show);
		m_show_registered = false;
	}
	if (hide_registered) {
		unregister_kprobe(&kp_s_show);
		hide_registered = false;
	}
	/* The /sys/module rules are ours: drop them here, not in sus_path's teardown - this layer cleans up what it registered. */
	hide_modules_commit(hide_modules_applied, 0);
	hide_modules_sync_sysfs();
	SUSFS_LOGI("susfs_hide_syms: exit enter=%d hit=%d layout_bad=%d (module lines=%d listed modules' syms=%d)\n",
		atomic_read(&hide_enter_count), atomic_read(&hide_hit_count),
		atomic_read(&hide_layout_bad),
		atomic_read(&n_modlines_skipped), atomic_read(&n_kallsyms_mod_skipped));
}
