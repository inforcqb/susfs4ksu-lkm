// SPDX-License-Identifier: GPL-2.0

#include <linux/module.h>
#include <linux/kprobes.h>
#include <linux/fs.h>
#include <linux/cred.h>
#include <linux/namei.h>
#include <linux/dcache.h>
#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include <linux/uaccess.h>
#include "mount.h"		/* fs/mount.h: real_mount() -> mnt_id */
#include <linux/atomic.h>	/* reverse-disguise hit counters */
#include <linux/mm.h>		/* struct vm_area_struct (the maps reverse face) */
#include <linux/kdev_t.h>	/* MAJOR/MINOR, to render dev:ino the way proc does */
#include <linux/kernel.h>	/* scnprintf, for the same rendering */
#include <linux/security.h>	/* security_secctx_to_secid */
#include "susfs_abi.h"
#include "susfs_log.h"
#include "susfs.h"		/* susfs_expose_proc, sus_path_lsm_active */
#include "symbol_resolver.h"	/* find_kernel_symbol_exact */
#include "ksu_umount_gate.h"	/* susfs_is_current_proc_umounted_app (issue #34) */

#define SUS_OR_MAX 64

#define OR_PATH_MAX 256

/* UID_SCHEME lives in susfs_abi.h, mirroring upstream susfs.h, where the enum sits next to the ABI structs. */

#ifndef FUSE_SUPER_MAGIC
#define FUSE_SUPER_MAGIC 0x65735546
#endif

/* Upstream's app threshold (susfs_def.h:122-125: TIF_PROC_UMOUNTED && current_uid().val >= 10000) is not a macro any
 * more: both gates that used it go through susfs_is_current_proc_umounted_app(), whose uid half is that literal 10000
 * (ksu_umount_gate.h) and whose other half is KernelSU's answer. */

static char or_su_ctx[128] = "u:r:ksu:s0";
module_param_string(or_su_ctx, or_su_ctx, sizeof(or_su_ctx), 0644);

static u32 or_su_sid;

static void (*or_cred_getsecid)(const struct cred *cred, u32 *secid);

struct sus_or_entry {
	char target_pathname[OR_PATH_MAX];
	char redirected_pathname[OR_PATH_MAX];
	unsigned long target_ino;
	dev_t target_dev;
	/* Reverse direction: the redirected inode is the lookup key, and target_path is what the reporters above show instead. */
	unsigned long redirected_ino;
	dev_t redirected_dev;

	unsigned long target_mnt_id;
	/* Cached at add time, base references held for the entry's lifetime. */
	struct path target_path;
	struct path redirected_path;
	int uid_scheme;

	bool dead;
};

static struct sus_or_entry or_entries[SUS_OR_MAX];
static int nor;
static DEFINE_MUTEX(or_lock);

static atomic_t or_rev_dpath_hits = ATOMIC_INIT(0);
static atomic_t or_rev_statfs_hits = ATOMIC_INIT(0);

static void or_resolve_su_sid(void)
{
	int err;

	if (or_su_sid)
		return;
	if (!or_su_ctx[0])
		return;
	err = security_secctx_to_secid(or_su_ctx, strlen(or_su_ctx), &or_su_sid);
	if (err) {
		pr_warn("open_redirect: secctx_to_secid(%s) failed %d\n",
			or_su_ctx, err);
		or_su_sid = 0;
		return;
	}
	SUSFS_LOGI("open_redirect: su ctx \"%s\" -> sid %u (stock KernelSU uses \"u:r:su:s0\", override with susfs_guard_lkm.or_su_ctx)\n",
		or_su_ctx, or_su_sid);
}

static __nocfi bool or_in_su_domain(void)
{
	u32 sid = 0;

	if (!or_cred_getsecid || !or_su_sid)
		return false;
	/* interrupt context: reading current->cred and walking the (static) LSM hook list never sleeps. */
	or_cred_getsecid(current_cred(), &sid);
	return sid == or_su_sid;
}

/* Upstream's reverse-disguise gate, verbatim in shape: SUSFS_IS_INODE_OPEN_REDIRECT (susfs_def.h:148-151) = flag bit AND
 * susfs_is_current_proc_umounted_app().  TIF_PROC_UMOUNTED is set by the SUSFS-patched KernelSU, which this kernel does not
 * have, so the app half is KernelSU's own ksu_uid_should_umount() answer (ksu_umount_gate.h, issue #34) rather than the
 * `uid >= 10000` proxy that also covered the manager and su-granted apps. */
static bool or_reverse_visible(void)
{
	return susfs_is_current_proc_umounted_app();
}

/* uid_scheme decision, mirroring upstream's switch in susfs_open_redirect_spoof_do_sys_openat() (susfs.c:941-964). */
static bool or_uid_matches(int scheme)
{
	switch (scheme) {
	case UID_NON_APP_PROC:			/* susfs.c:942-945 */
		return current_uid().val % 100000 < 10000;
	case UID_ROOT_PROC_EXCEPT_SU_PROC:	/* susfs.c:946-949 */
		return current_uid().val == 0 && !or_in_su_domain();
	case UID_NON_SU_PROC:			/* susfs.c:950-953 */
		return !or_in_su_domain();
	case UID_UMOUNTED_APP_PROC:		/* susfs.c:954-957 */
	case UID_UMOUNTED_PROC:			/* susfs.c:958-961 */
		/* Upstream: test_thread_flag(TIF_PROC_UMOUNTED) [&& uid >= 10000 for the _APP variant] (susfs_def.h:98-125).  The
		 * flag is set by the SUSFS-patched KernelSU, so both schemes ask KernelSU the same question here
		 * (susfs_is_current_proc_umounted_app(), ksu_umount_gate.h, issue #34) and still degenerate into one predicate - a
		 * strictly narrower gate than scheme 2, as upstream's flag is. */
		return susfs_is_current_proc_umounted_app();
	default:				/* susfs.c:962-963 */
		return false;
	}
}

static struct sus_or_entry *or_find_by_path(const char *target)
{
	int i;

	for (i = 0; i < nor; i++) {
		if (READ_ONCE(or_entries[i].dead))
			continue;
		if (!strcmp(or_entries[i].target_pathname, target))
			return &or_entries[i];
	}
	return NULL;
}

static struct sus_or_entry *or_find_by_inode(unsigned long ino, dev_t dev)
{
	int i;

	for (i = 0; i < nor; i++) {

		if (READ_ONCE(or_entries[i].dead))
			continue;
		smp_rmb();
		if (or_entries[i].target_ino == ino &&
		    or_entries[i].target_dev == dev)
			return &or_entries[i];
	}
	return NULL;
}

/* Reverse direction: keyed on the redirected (really opened) inode, published like or_find_by_inode(). */
static struct sus_or_entry *or_find_by_redirected_inode(unsigned long ino, dev_t dev)
{
	int i;

	for (i = 0; i < nor; i++) {
		if (READ_ONCE(or_entries[i].dead))
			continue;
		smp_rmb();
		if (or_entries[i].redirected_ino == ino &&
		    or_entries[i].redirected_dev == dev)
			return &or_entries[i];
	}
	return NULL;
}

bool susfs_open_redirect_spoof_ids(unsigned long ino, unsigned long *out_ino,
				   unsigned long *out_mnt_id)
{
	struct sus_or_entry *e = NULL;
	int i, hits = 0;

	if (!ino || !out_ino || !or_reverse_visible())
		return false;
	for (i = 0; i < nor; i++) {
		if (READ_ONCE(or_entries[i].dead))
			continue;
		smp_rmb();
		if (or_entries[i].redirected_ino != ino)
			continue;
		e = &or_entries[i];
		if (++hits > 1)
			return false;
	}
	if (hits != 1)
		return false;
	*out_ino = e->target_ino;
	if (out_mnt_id)
		*out_mnt_id = e->target_mnt_id;
	return true;
}

static bool or_is_redirected_path(const char *target)
{
	int i;

	for (i = 0; i < nor; i++) {
		if (READ_ONCE(or_entries[i].dead))
			continue;
		if (!strcmp(or_entries[i].redirected_pathname, target))
			return true;
	}
	return false;
}

static int or_vfs_open_pre(struct kprobe *kp, struct pt_regs *regs)
{
	const struct path *path = (const struct path *)regs->regs[0];
	struct inode *inode;
	struct sus_or_entry *e;

	if (IS_ERR_OR_NULL(path) || !path->dentry)
		return 0;
	inode = d_backing_inode(path->dentry);
	if (!inode)
		return 0;

	e = or_find_by_inode(inode->i_ino, inode->i_sb->s_dev);
	if (!e)
		return 0;
	if (!or_uid_matches(e->uid_scheme))
		return 0;

	/* vfs_open does file->f_path = *path; do_dentry_open path_get()s it. */
	regs->regs[0] = (unsigned long)&e->redirected_path;
	return 0;
}

static bool or_dpath_swap(struct pt_regs *regs)
{
	const struct path *path = (const struct path *)regs->regs[0];
	struct inode *inode;
	struct sus_or_entry *e;

	if (!READ_ONCE(nor) || IS_ERR_OR_NULL(path) || !path->dentry)
		return false;
	if (!or_reverse_visible())
		return false;
	inode = d_backing_inode(path->dentry);
	if (!inode)
		return false;

	e = or_find_by_redirected_inode(inode->i_ino, inode->i_sb->s_dev);
	if (!e)
		return false;

	regs->regs[0] = (unsigned long)&e->target_path;
	return true;
}

static int or_dpath_pre(struct kprobe *kp, struct pt_regs *regs)
{
	if (or_dpath_swap(regs))
		atomic_inc(&or_rev_dpath_hits);
	return 0;
}

static int or_vfs_statfs_pre(struct kprobe *kp, struct pt_regs *regs)
{
	const struct path *path = (const struct path *)regs->regs[0];
	struct inode *inode;
	struct sus_or_entry *e;

	if (!READ_ONCE(nor) || IS_ERR_OR_NULL(path) || !path->dentry)
		return 0;
	if (!or_reverse_visible())
		return 0;
	inode = d_backing_inode(path->dentry);
	if (!inode)
		return 0;

	e = or_find_by_redirected_inode(inode->i_ino, inode->i_sb->s_dev);
	if (!e)
		return 0;

	atomic_inc(&or_rev_statfs_hits);
	regs->regs[0] = (unsigned long)&e->target_path;
	return 0;
}

static struct kprobe kp_or = {
	.symbol_name = "vfs_open",
	.pre_handler = or_vfs_open_pre,
};

static struct kprobe kp_or_dpath = {
	.symbol_name = "d_path",
	.pre_handler = or_dpath_pre,
};

static struct kprobe kp_or_vfs_statfs = {
	.symbol_name = "vfs_statfs",
	.pre_handler = or_vfs_statfs_pre,
};

static atomic_t or_rev_maps_hits = ATOMIC_INIT(0);
static atomic_t or_rev_maps_rewrites = ATOMIC_INIT(0);	/* the maj:min ino run */
static atomic_t or_rev_maps_names = ATOMIC_INIT(0);	/* the name column */

struct or_maps_args {
	struct seq_file *m;
	struct vm_area_struct *vma;
};

static int or_maps_entry(struct kretprobe_instance *ri, struct pt_regs *regs)
{
	struct or_maps_args *a = (struct or_maps_args *)ri->data;

	a->m = (struct seq_file *)regs->regs[0];
	a->vma = (struct vm_area_struct *)regs->regs[1];
	return 0;
}

static bool or_buf_replace(struct seq_file *m, const char *old, size_t old_len,
			   const char *new, size_t new_len)
{
	char *buf = m->buf;
	size_t count = m->count, i, pos = 0;

	if (!old_len || !new_len || old_len > count)
		return false;
	for (i = 0; i + old_len <= count; i++) {
		if (!memcmp(buf + i, old, old_len)) {
			pos = i;
			break;
		}
	}
	if (i + old_len > count)
		return false;
	if (new_len > old_len && count + (new_len - old_len) >= m->size)
		return false;
	if (new_len != old_len)
		memmove(buf + pos + new_len, buf + pos + old_len, count - (pos + old_len));
	memcpy(buf + pos, new, new_len);
	m->count = count - old_len + new_len;
	return true;
}

static int or_maps_ret(struct kretprobe_instance *ri, struct pt_regs *regs)
{
	const struct or_maps_args *a = (const struct or_maps_args *)ri->data;
	struct seq_file *m = a->m;
	struct vm_area_struct *vma = a->vma;
	struct inode *inode;
	struct sus_or_entry *e;
	char old[48], new[48];
	int old_len, new_len;

	if (!susfs_ptr_plausible(m) || !susfs_ptr_plausible(vma) ||
	    !m->buf || !m->count || !vma->vm_file)
		return 0;
	if (!or_reverse_visible())
		return 0;
	inode = file_inode(vma->vm_file);
	if (!inode)
		return 0;

	e = or_find_by_redirected_inode(inode->i_ino, inode->i_sb->s_dev);
	if (!e)
		return 0;

	atomic_inc(&or_rev_maps_hits);

	old_len = scnprintf(old, sizeof(old), "%02x:%02x %lu",
			    (unsigned int)MAJOR(inode->i_sb->s_dev),
			    (unsigned int)MINOR(inode->i_sb->s_dev),
			    (unsigned long)inode->i_ino);
	new_len = scnprintf(new, sizeof(new), "%02x:%02x %lu",
			    (unsigned int)MAJOR(e->target_dev),
			    (unsigned int)MINOR(e->target_dev),
			    (unsigned long)e->target_ino);

	while (new_len < old_len && new_len < (int)sizeof(new) - 1)
		new[new_len++] = ' ';
	if (old_len > 0 && new_len > 0 &&
	    or_buf_replace(m, old, (size_t)old_len, new, (size_t)new_len))
		atomic_inc(&or_rev_maps_rewrites);

	if (e->redirected_pathname[0] && e->target_pathname[0]) {
		size_t rlen = strlen(e->redirected_pathname);
		size_t tlen = strlen(e->target_pathname);

		if (or_buf_replace(m, e->redirected_pathname, rlen,
				   e->target_pathname, tlen))
			atomic_inc(&or_rev_maps_names);
	}
	return 0;
}

static struct kretprobe kr_or_maps = {
	.kp.symbol_name = "show_map_vma",	/* fs/proc/task_mmu.c */
	.entry_handler = or_maps_entry,
	.handler = or_maps_ret,
	.data_size = sizeof(struct or_maps_args),
	.maxactive = 16,
};
static bool or_maps_registered;

static atomic_t or_rev_fdinfo_hits = ATOMIC_INIT(0);
static atomic_t or_rev_fdinfo_rewrites = ATOMIC_INIT(0);

static int or_fdinfo_entry(struct kretprobe_instance *ri, struct pt_regs *regs)
{
	struct seq_file **slot = (struct seq_file **)ri->data;

	*slot = (struct seq_file *)regs->regs[0];
	return 0;
}

static bool or_fdinfo_find_dec(struct seq_file *m, const char *label, size_t label_len,
			       size_t *out_pos, size_t *out_len, unsigned long *out_val)
{
	char *buf = m->buf;
	size_t count = m->count, i, pos = 0, len = 0;
	unsigned long v = 0;

	for (i = 0; i + label_len < count; i++) {
		if (!memcmp(buf + i, label, label_len)) {
			pos = i + label_len;
			break;
		}
	}
	if (!pos)
		return false;
	while (pos + len < count && len < 10 &&
	       buf[pos + len] >= '0' && buf[pos + len] <= '9') {
		v = v * 10 + (unsigned long)(buf[pos + len] - '0');
		len++;
	}
	if (!len)
		return false;
	*out_pos = pos;
	*out_len = len;
	*out_val = v;
	return true;
}

static bool or_fdinfo_write_dec(struct seq_file *m, size_t pos, size_t len,
				unsigned long new_val)
{
	char digits[12];
	size_t count = m->count, i, n = 0;
	unsigned int v = (unsigned int)new_val;

	while (v) {
		digits[n++] = (char)('0' + v % 10);
		v /= 10;
	}
	if (!n)
		return false;
	if (n > len && count + (n - len) >= m->size)
		return false;
	for (i = 0; i < n / 2; i++) {
		char t = digits[i];

		digits[i] = digits[n - 1 - i];
		digits[n - 1 - i] = t;
	}
	if (n != len)
		memmove(m->buf + pos + n, m->buf + pos + len, count - (pos + len));
	memcpy(m->buf + pos, digits, n);
	m->count = count - len + n;
	return true;
}

static int or_fdinfo_ret(struct kretprobe_instance *ri, struct pt_regs *regs)
{
	struct seq_file *m = *(struct seq_file **)ri->data;
	size_t pos, len;
	unsigned long old = 0, new_ino = 0, new_mnt = 0;
	int rewrites = 0;

	if (!m || (long)regs_return_value(regs) != 0)
		return 0;
	if (!m->buf || !m->count)
		return 0;
	if (!or_reverse_visible())
		return 0;

	atomic_inc(&or_rev_fdinfo_hits);

	if (or_fdinfo_find_dec(m, "ino:\t", 5, &pos, &len, &old) &&
	    old && susfs_open_redirect_spoof_ids(old, &new_ino, &new_mnt) &&
	    new_ino != old && or_fdinfo_write_dec(m, pos, len, new_ino))
		rewrites++;

	if (new_mnt && or_fdinfo_find_dec(m, "mnt_id:\t", 8, &pos, &len, &old) &&
	    old != new_mnt && or_fdinfo_write_dec(m, pos, len, new_mnt))
		rewrites++;

	if (rewrites)
		atomic_inc(&or_rev_fdinfo_rewrites);
	return 0;
}

static struct kretprobe kr_or_fdinfo = {
	.kp.symbol_name = "seq_show",		/* fs/proc/fd.c */
	.entry_handler = or_fdinfo_entry,
	.handler = or_fdinfo_ret,
	.data_size = sizeof(struct seq_file *),
	.maxactive = 16,
};
static bool or_fdinfo_registered;

static bool or_registered;
static bool or_dpath_registered;
static bool or_statfs_registered;

static int or_register(void)
{
	int rc;

	if (or_registered)
		return 0;
	rc = register_kprobe(&kp_or);
	if (rc)
		return rc;
	or_registered = true;
	SUSFS_LOGI("susfs_open_redirect: hook installed (vfs_open)\n");
	return 0;
}

static void or_register_reverse(void)
{
	int rc;

	if (!or_dpath_registered) {
		rc = register_kprobe(&kp_or_dpath);
		if (rc)
			pr_warn("open_redirect: register_kprobe(d_path) failed %d - readlink not disguised (or already inlined)\n",
				rc);
		else {
			or_dpath_registered = true;
			SUSFS_LOGI("susfs_open_redirect: reverse hook installed (d_path)\n");
		}
	}

	if (!or_statfs_registered) {
		rc = register_kprobe(&kp_or_vfs_statfs);
		if (rc)
			pr_warn("open_redirect: register_kprobe(vfs_statfs) failed %d - statfs not disguised (or already inlined)\n",
				rc);
		else {
			or_statfs_registered = true;
			SUSFS_LOGI("susfs_open_redirect: reverse hook installed (vfs_statfs)\n");
		}
	}
	if (!or_maps_registered) {
		rc = register_kretprobe(&kr_or_maps);
		if (rc)
			pr_warn("open_redirect: register_kretprobe(show_map_vma) failed %d - the maps dev:ino stays the redirected file's\n",
				rc);
		else {
			or_maps_registered = true;
			SUSFS_LOGI("susfs_open_redirect: reverse hook installed (show_map_vma)\n");
		}
	}
	if (!or_fdinfo_registered) {
		rc = register_kretprobe(&kr_or_fdinfo);
		if (rc)
			pr_warn("open_redirect: register_kretprobe(seq_show) failed %d - fdinfo names the redirected inode\n",
				rc);
		else {
			or_fdinfo_registered = true;
			SUSFS_LOGI("susfs_open_redirect: reverse hook installed (seq_show/fdinfo)\n");
		}
	}
}

static void or_unregister(void)
{
	if (or_fdinfo_registered) {
		unregister_kretprobe(&kr_or_fdinfo);
		or_fdinfo_registered = false;
	}
	if (or_maps_registered) {
		unregister_kretprobe(&kr_or_maps);
		or_maps_registered = false;
	}
	if (or_statfs_registered) {
		unregister_kprobe(&kp_or_vfs_statfs);
		or_statfs_registered = false;
	}
	if (or_dpath_registered) {
		unregister_kprobe(&kp_or_dpath);
		or_dpath_registered = false;
	}

	if (!or_registered)
		return;
	unregister_kprobe(&kp_or);
	or_registered = false;
	SUSFS_LOGI("susfs_open_redirect: hook removed\n");
}

/* ---- /proc/susfs_open_redirect ---- */
static int or_proc_show(struct seq_file *m, void *v);
static int or_proc_open(struct inode *inode, struct file *file);
static ssize_t or_proc_write(struct file *file, const char __user *buf,
			     size_t len, loff_t *off);

static const struct proc_ops or_proc_ops = {
	.proc_open = or_proc_open,
	.proc_read = seq_read,
	.proc_write = or_proc_write,
	.proc_lseek = seq_lseek,
	.proc_release = single_release,
};

static struct proc_dir_entry *or_proc_entry;

int susfs_open_redirect_init(void)
{
	or_cred_getsecid =
		(void *)find_kernel_symbol_exact("security_cred_getsecid");
	if (!or_cred_getsecid)
		pr_warn("open_redirect: security_cred_getsecid not found - schemes 1/2 will be refused\n");
	or_resolve_su_sid();

	if (susfs_control_node_allowed()) {
		or_proc_entry = proc_create("susfs_open_redirect", 0777, NULL,
					    &or_proc_ops);
		if (!or_proc_entry)
			pr_warn("proc_create(susfs_open_redirect) failed\n");
	} else {
		SUSFS_LOGI("susfs_open_redirect: /proc node not created (expose_proc=%d lsm=%d)\n",
			(int)susfs_expose_proc, (int)sus_path_lsm_active());
	}

	SUSFS_LOGI("susfs_open_redirect: %d rules (hook %s, proc %d)\n", nor,
		or_registered ? "armed" : "lazy", or_proc_entry != NULL);
	return 0;
}

void susfs_open_redirect_exit(void)
{
	int i;

	or_unregister();
	if (or_proc_entry) {
		proc_remove(or_proc_entry);
		or_proc_entry = NULL;
	}

	for (i = 0; i < nor; i++) {
		path_put(&or_entries[i].redirected_path);
		or_entries[i].redirected_path.dentry = NULL;
		or_entries[i].redirected_path.mnt = NULL;
		path_put(&or_entries[i].target_path);
		or_entries[i].target_path.dentry = NULL;
		or_entries[i].target_path.mnt = NULL;
		or_entries[i].dead = true;
	}
	nor = 0;
}

static int or_proc_show(struct seq_file *m, void *v)
{
	int i;

	mutex_lock(&or_lock);
	if (nor == 0) {
		seq_puts(m, "(empty)\n");
	} else {
		for (i = 0; i < nor; i++) {
			if (READ_ONCE(or_entries[i].dead))
				continue;
			seq_printf(m, "%s -> %s uid=%d (ino=%lu dev=%lu mnt=%lu | rev: ino=%lu dev=%lu)\n",
				   or_entries[i].target_pathname,
				   or_entries[i].redirected_pathname,
				   or_entries[i].uid_scheme,
				   or_entries[i].target_ino,
				   (unsigned long)or_entries[i].target_dev,
				   or_entries[i].target_mnt_id,
				   or_entries[i].redirected_ino,
				   (unsigned long)or_entries[i].redirected_dev);
		}
	}

	seq_printf(m, "hooks: open=%d dpath=%d statfs=%d maps=%d fdinfo=%d | rev hits: dpath=%d statfs=%d maps=%d/%d/%d fdinfo=%d/%d | su_sid=%u\n",
		   or_registered, or_dpath_registered, or_statfs_registered,
		   or_maps_registered, or_fdinfo_registered,
		   atomic_read(&or_rev_dpath_hits),
		   atomic_read(&or_rev_statfs_hits),
		   atomic_read(&or_rev_maps_hits),
		   atomic_read(&or_rev_maps_rewrites),
		   atomic_read(&or_rev_maps_names),
		   atomic_read(&or_rev_fdinfo_hits),
		   atomic_read(&or_rev_fdinfo_rewrites),
		   or_su_sid);
	mutex_unlock(&or_lock);
	return 0;
}

static int or_proc_open(struct inode *inode, struct file *file)
{

	if (current_uid().val != 0)
		return -ENOENT;
	return single_open(file, or_proc_show, NULL);
}

static int split_ws(char *buf, char **argv, int max)
{
	int argc = 0;
	char *p = buf;

	while (argc < max) {
		while (*p == ' ' || *p == '\t' || *p == '\n')
			p++;
		if (*p == '\0')
			break;
		argv[argc++] = p;
		while (*p && *p != ' ' && *p != '\t' && *p != '\n')
			p++;
		if (*p)
			*p++ = '\0';
	}
	return argc;
}

static int or_add(const char *target, const char *redirected, int scheme)
{
	struct sus_or_entry *e;
	struct path tp, rp;
	struct inode *ti, *ri;
	int rc;

	/* upstream susfs.c:792-796 */
	if (scheme < UID_NON_APP_PROC || scheme > UID_UMOUNTED_PROC)
		return -EINVAL;

	if (!susfs_abi_path_ok(target, OR_PATH_MAX) ||
	    !susfs_abi_path_ok(redirected, OR_PATH_MAX))
		return -ENAMETOOLONG;

	rc = kern_path(target, LOOKUP_FOLLOW, &tp);
	if (rc)
		return rc;
	ti = d_backing_inode(tp.dentry);
	if (!ti) {
		path_put(&tp);
		return -ENOENT;
	}

	/* resolve redirected and CACHE it (base ref kept for entry lifetime) */
	rc = kern_path(redirected, LOOKUP_FOLLOW, &rp);
	if (rc) {
		path_put(&tp);
		return rc;
	}
	ri = d_backing_inode(rp.dentry);
	if (!ri) {
		path_put(&rp);
		path_put(&tp);
		return -ENOENT;
	}

	if (tp.dentry->d_sb->s_magic == FUSE_SUPER_MAGIC ||
	    rp.dentry->d_sb->s_magic == FUSE_SUPER_MAGIC) {
		pr_warn("open_redirect: FUSE fs is not supported for open_redirect feature\n");
		path_put(&rp);
		path_put(&tp);
		return -EINVAL;
	}

	if (scheme == UID_ROOT_PROC_EXCEPT_SU_PROC ||
	    scheme == UID_NON_SU_PROC) {
		or_resolve_su_sid();
		if (!or_su_sid) {
			pr_warn("open_redirect: scheme %d needs a resolvable su domain - set or_su_ctx=u:r:su:s0 (currently \"%s\")\n",
				scheme, or_su_ctx);
			path_put(&rp);
			path_put(&tp);
			return -EOPNOTSUPP;
		}
	}

	rc = or_register();
	if (rc) {
		path_put(&rp);
		path_put(&tp);
		pr_warn("open_redirect: hook registration failed %d\n", rc);
		return rc;
	}
	or_register_reverse();

	e = or_find_by_path(target);
	if (!e && or_is_redirected_path(target)) {
		pr_warn("open_redirect: '%s' cannot be added because it is used for reversed lookup only\n",
			target);
		path_put(&rp);
		path_put(&tp);
		return -EINVAL;
	}

	/* Capacity is checked before the rewrite retires anything: with a full table, failing after
	 * the WRITE_ONCE(e->dead, ...) below would return -ENOSPC *and* silently kill the
	 * redirection that was working. */
	if (nor >= SUS_OR_MAX) {
		path_put(&rp);
		path_put(&tp);
		return -ENOSPC;
	}

	if (e) {

		WRITE_ONCE(e->dead, true);
		smp_wmb();
		e = NULL;
	}

	e = &or_entries[nor++];
	/* nor++ takes the slot before a single field is in it, and a never-used slot is already
	 * dead == false, so the clear at the end cannot keep a reader out - a reader keyed on the
	 * real (ino, dev) would hand vfs_open() a path whose dentry is still NULL.  Dead first. */
	WRITE_ONCE(e->dead, true);
	smp_wmb();
	strscpy(e->target_pathname, target, OR_PATH_MAX);

	strscpy(e->redirected_pathname, redirected, OR_PATH_MAX);
	e->target_ino = ti->i_ino;
	e->target_dev = ti->i_sb->s_dev;
	e->target_mnt_id = (unsigned long)real_mount(tp.mnt)->mnt_id;
	e->redirected_ino = ri->i_ino;
	e->redirected_dev = ri->i_sb->s_dev;
	e->redirected_path = rp;   /* transfer the cached references */
	e->target_path = tp;
	e->uid_scheme = scheme;
	smp_wmb();
	WRITE_ONCE(e->dead, false);	/* publish last: readers key off this */

	return 0;			/* both path references now belong to e */
}

static void or_del(const char *target)
{
	struct sus_or_entry *e;

	e = or_find_by_path(target);
	if (!e)
		return;

	WRITE_ONCE(e->dead, true);
	smp_wmb();

	e->target_pathname[0] = '\0';
	e->redirected_pathname[0] = '\0';
}

static ssize_t or_proc_write(struct file *file, const char __user *buf,
			     size_t len, loff_t *off)
{
	char cmd[640];
	char *argv[8];
	int argc, err;
	long scheme;

	/* Same gate as or_proc_open(): an fd opened before the opener dropped privileges must not become a way in. */
	if (current_uid().val != 0)
		return -ENOENT;

	if (len >= sizeof(cmd))
		len = sizeof(cmd) - 1;
	if (copy_from_user(cmd, buf, len))
		return -EFAULT;
	cmd[len] = 0;

	argc = split_ws(cmd, argv, 8);
	if (argc == 0)
		return len;

	mutex_lock(&or_lock);
	err = -EINVAL;

	if (!strcmp(argv[0], "add_open_redirect") && argc == 4) {
		if (kstrtol(argv[3], 10, &scheme))
			err = -EINVAL;
		else
			err = or_add(argv[1], argv[2], (int)scheme);
	} else if (!strcmp(argv[0], "del") && argc == 2) {
		or_del(argv[1]);
		err = 0;
	} else if (!strcmp(argv[0], "clear")) {
		int i;

		for (i = 0; i < nor; i++) {
			if (READ_ONCE(or_entries[i].dead))
				continue;
			or_del(or_entries[i].target_pathname);
		}
		err = 0;
	}

	mutex_unlock(&or_lock);

	if (err) {
		pr_warn("open_redirect proc write '%s' -> err %d\n", argv[0], err);
		return err;	/* surface the failure; success keeps returning len */
	}
	return len;
}

/* supercall: CMD_SUSFS_ADD_OPEN_REDIRECT */
void susfs_open_redirect_supercall(void __user **arg)
{
	struct st_susfs_open_redirect info = {0};
	int err;

	if (copy_from_user(&info, (void __user *)*arg, sizeof(info))) {
		info.err = -EFAULT;
		goto out;
	}

	mutex_lock(&or_lock);
	err = or_add(info.target_pathname, info.redirected_pathname,
		     info.uid_scheme);
	mutex_unlock(&or_lock);
	info.err = err;
out:
	/* upstream writes back only ->err for input-type commands */
	if (copy_to_user(&((struct st_susfs_open_redirect __user *)*arg)->err,
			 &info.err, sizeof(info.err)))
		pr_warn("open_redirect supercall copy_to_user failed\n");
}
