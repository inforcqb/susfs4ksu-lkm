// SPDX-License-Identifier: GPL-2.0

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

static int hide_modules_format(char *buf, size_t size)
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

/* ---- the two frontends ---- */

static int hide_modules_param_set(const char *val, const struct kernel_param *kp)
{
	/* insmod passes a bare value, so the parameter accepts a command-less list. */
	return hide_modules_command(val, true);
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

	if (strstr(name, "ksu") || strstr(name, "susfs"))
		return true;

	return false;
}

static atomic_t hide_hit_count = ATOMIC_INIT(0);
static atomic_t hide_enter_count = ATOMIC_INIT(0);
static atomic_t hide_layout_bad = ATOMIC_INIT(0);

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

static struct kprobe kp_s_show = {
	.symbol_name = "s_show",
	.pre_handler = hide_syms_s_show_pre,
};

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

	rc = register_kprobe(&kp_s_show);
	if (rc) {
		pr_warn("susfs_hide_syms: register_kprobe(s_show) failed %d\n", rc);
		return rc;
	}
	hide_registered = true;

	table_show = hide_syms_table_show();

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

	{
		char staged[HIDE_MODULES_MAX][MODULE_NAME_LEN] = { { 0 } };

		strscpy(staged[0], SUSFS_LKM_MODULE_NAME, MODULE_NAME_LEN);
		hide_modules_commit(staged, 1);
	}
	hide_modules_sync_sysfs();

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
