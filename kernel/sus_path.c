// SPDX-License-Identifier: GPL-2.0

#include <linux/module.h>
#include <linux/delay.h>	/* ndelay, for the timing cover */
#include <linux/random.h>	/* prandom_u32_max, for its jitter */
#include <linux/tracepoint.h>
#include <trace/events/syscalls.h>
#include <asm/syscall.h>
#include <linux/uaccess.h>
#include <linux/syscalls.h>
#include <linux/slab.h>
#include <linux/string.h>
#include <linux/list.h>
#include <linux/spinlock.h>
#include <linux/namei.h>
#include <linux/fs.h>
#include <linux/err.h>
#include <linux/compat.h>
#include <linux/workqueue.h>	/* the pending-resolution retry timer */
#include <linux/mutex.h>	/* serialises the first rule's arming */
#include <linux/limits.h>
#include <linux/cred.h>
#include <linux/atomic.h>
#include <linux/proc_fs.h>	/* proc_create() for /proc/susfs_path */
#include <linux/seq_file.h>	/* single_open()/seq_write() for the same node */
#include <linux/version.h>	/* LINUX_VERSION_CODE: the setxattr hook's first argument */
#include "susfs_abi.h"
#include "susfs_log.h"
#include "susfs.h"	/* susfs_abi_path_ok */
#include "symbol_resolver.h"	/* find_kernel_symbol_exact, for optional compat probes */

#include "lsm_hook.h"

#define DIRENT_BUF_SIZE 65536
#define SUS_PATH_MAX_ENTRIES 8192

#define SUS_PATH_PENDING_RETRY_S 2
#define SUS_PATH_PENDING_TRIES 60
#define SUS_PATH_PENDING_BUDGET 128
/* Longest registered path; 256 matches the ABI's target_pathname field. */
#define SUS_PATH_LEN 256

/* Directory-listing syscall numbers.
 *
 * The native one is this build tree's own UAPI macro (<asm/unistd.h> via syscalls.h): syscall
 * numbers are ABI, not per-device - every arm64 kernel from 5.10 to 6.18 numbers getdents64 61,
 * because userspace binaries have the number baked into their SVC sequence.  The AArch32 pair
 * has no macro in an arm64 tree, so it is written out from the 32-bit ARM table
 * (arch/arm/tools/syscall.tbl): getdents 141, getdents64 217.
 *
 * A number on its own still does not identify the call, and the two tables collide by design:
 * arm64's native 141 is getpriority, its 106 delete_module, its 217 add_key, and its
 * 195/196/197 shmctl/shmat/shmdt, while AArch32 gives 141/217 to the two getdents and
 * 195/196/197 to stat64/lstat64/fstat64.  Every match is therefore gated on the caller's ABI -
 * here in sus_path_dirent_layout_id(), and the same way in susfs_kstat.c for the stat family. */
#define SUS_NR_GETDENTS64_COMPAT 217
#define SUS_NR_GETDENTS_COMPAT   141

struct linux_dirent64 {
    u64 d_ino;
    s64 d_off;
    unsigned short d_reclen;
    unsigned char d_type;
    char d_name[];
};

struct sus_path_entry {
    struct list_head list;

    struct inode *inode;
    u64 dev;
    u64 ino;
    char name[NAME_MAX + 1];

    char path[SUS_PATH_LEN];
    unsigned int path_len;

    unsigned int pass;

    bool self_protect;
    /* Pre-relax mode, 0 = this rule did not touch it (sus_path_relax_mode()). */
    umode_t orig_mode;
};

static void sus_path_relax_mode(struct sus_path_entry *e)
{
    umode_t mode;

    if (!e->inode)
        return;

    mode = READ_ONCE(e->inode->i_mode);
    if ((mode & (S_IRWXU | S_IRWXG | S_IRWXO)) == 0777)
        return;                 /* already open, or another rule did it */

    e->orig_mode = mode;
    WRITE_ONCE(e->inode->i_mode, (mode & ~(umode_t)(S_IRWXU | S_IRWXG | S_IRWXO)) | 0777);
}

static void sus_path_restore_mode(struct sus_path_entry *e)
{
    if (!e->inode || !e->orig_mode)
        return;

    WRITE_ONCE(e->inode->i_mode, e->orig_mode);
    e->orig_mode = 0;
}

static void sus_path_entry_set_path(struct sus_path_entry *e, const char *path);

static LIST_HEAD(sus_path_list);
static DEFINE_SPINLOCK(sus_path_lock);
static unsigned int sus_path_count;

static atomic_t sus_path_n_pending = ATOMIC_INIT(0);
static unsigned int sus_path_pass_gen;      /* guarded by sus_path_lock */
static atomic_t sus_path_pending_tries = ATOMIC_INIT(0);

static DEFINE_MUTEX(sus_path_pending_lock);

static void sus_path_pending_work(struct work_struct *w);
static DECLARE_DELAYED_WORK(sus_path_pending_wq, sus_path_pending_work);

/* legacy/debug: hide a single exact filename everywhere (empty = disabled) */
static char hide_name[NAME_MAX + 1];
module_param_string(hide_name, hide_name, sizeof(hide_name), 0644);

static char *dirent_tmp;

static int no_extra;
module_param(no_extra, int, 0644);

static DEFINE_SPINLOCK(sus_path_buf_lock);

static atomic_t n_dirent_rewrite_fail = ATOMIC_INIT(0);

static atomic_t n_dirent_all_hidden = ATOMIC_INIT(0);

static struct task_struct *sus_path_resolver;

static inline bool sus_path_is_resolver(void)
{
    return READ_ONCE(sus_path_resolver) == current;
}

static const struct cred *sus_path_pending_cred;
static DEFINE_MUTEX(sus_path_cred_lock);
static atomic_t sus_path_used_caller_cred = ATOMIC_INIT(0);

/* Called from the supercall (process context) when a rule is registered pending. */
static void sus_path_save_caller_cred(void)
{
    const struct cred *new = get_cred(current_cred());
    const struct cred *old;

    mutex_lock(&sus_path_cred_lock);
    old = sus_path_pending_cred;
    sus_path_pending_cred = new;
    mutex_unlock(&sus_path_cred_lock);
    if (old)
        put_cred(old);
}

static const struct cred *sus_path_override_creds(const struct cred **borrowed)
{
    const struct cred *cred;

    *borrowed = NULL;
    mutex_lock(&sus_path_cred_lock);
    cred = sus_path_pending_cred;
    if (cred)
        get_cred(cred);
    mutex_unlock(&sus_path_cred_lock);
    if (!cred)
        return NULL;

    *borrowed = cred;
    atomic_inc(&sus_path_used_caller_cred);
    return override_creds(cred);
}

static void sus_path_revert_creds(const struct cred *saved, const struct cred *borrowed)
{
    if (saved)
        revert_creds(saved);
    if (borrowed)
        put_cred(borrowed);
}

static void sus_path_drop_caller_cred(void)
{
    const struct cred *old;

    mutex_lock(&sus_path_cred_lock);
    old = sus_path_pending_cred;
    sus_path_pending_cred = NULL;
    mutex_unlock(&sus_path_cred_lock);
    if (old)
        put_cred(old);
}

static atomic_t sus_path_pend_passes = ATOMIC_INIT(0);      /* resolve passes run */
static atomic_t sus_path_pend_ticks = ATOMIC_INIT(0);       /* timer ticks run */
static atomic_t sus_path_pend_walks = ATOMIC_INIT(0);       /* walks that succeeded */
static atomic_t sus_path_pend_lost = ATOMIC_INIT(0);        /* walk ok, rule gone */
static atomic_t sus_path_pend_last_rc = ATOMIC_INIT(0);     /* last walk result */
static atomic_t sus_path_pend_logged_rc = ATOMIC_INIT(1);   /* rc already reported */

static int hide_from_apps = 1;
module_param(hide_from_apps, int, 0644);

static inline bool sus_path_gate_uid_ok(void)
{
    if (!hide_from_apps)
        return true;
    return current_uid().val >= 10000;
}

static inline bool sus_path_gate_ok(struct inode *inode)
{
    if (!hide_from_apps)
        return true;
    if (current_uid().val < 10000)
        return false;
    return current_uid().val != inode->i_uid.val;
}

static inline bool sus_path_entry_gate_inode(const struct sus_path_entry *e,
                                             struct inode *inode)
{
    if (e->self_protect)
        return current_uid().val != 0;
    return sus_path_gate_ok(inode);
}

static inline bool sus_path_entry_gate_any(const struct sus_path_entry *e)
{
    if (e->self_protect)
        return current_uid().val != 0;
    if (!e->inode)
        return sus_path_gate_uid_ok();
    return sus_path_gate_ok(e->inode);
}

static bool sus_path_is_hidden(u64 ino, const char *name)
{
    struct sus_path_entry *e;
    bool hidden = false;

    if (sus_path_is_resolver())
        return false;

    if (ino) {
        spin_lock(&sus_path_lock);
        list_for_each_entry(e, &sus_path_list, list) {
            if (e->ino && e->ino == ino && !strcmp(e->name, name) &&
                sus_path_entry_gate_any(e)) {
                hidden = true;
                break;
            }
        }
        spin_unlock(&sus_path_lock);
    }

    if (!hidden && hide_name[0])
        hidden = !strcmp(name, hide_name);

    return hidden;
}

static void sus_path_basename(const char *path, char *dst, size_t size)
{
    const char *slash = strrchr(path, '/');

    if (slash && slash[1])
        path = slash + 1;
    strscpy(dst, path, size);
}

static int sus_path_resolve_pending(void)
{
    char path[SUS_PATH_LEN];
    unsigned int gen;
    int budget = SUS_PATH_PENDING_BUDGET;
    int resolved = 0;

    if (!atomic_read(&sus_path_n_pending))
        return 0;
    /* trylock: the supercall must never block behind a pass sleeping in kern_path(). */
    if (!mutex_trylock(&sus_path_pending_lock))
        return 0;
    atomic_inc(&sus_path_pend_passes);

    /* Pass marker.  0 means "never attempted", so generation 0 is skipped. */
    spin_lock(&sus_path_lock);
    gen = ++sus_path_pass_gen;
    if (!gen)
        gen = ++sus_path_pass_gen;
    spin_unlock(&sus_path_lock);

    while (budget-- > 0) {
        struct sus_path_entry *e, *slot;
        struct inode *inode = NULL;
        const struct cred *saved;
        const struct cred *borrowed = NULL;
        struct path p;
        char name[NAME_MAX + 1];
        bool published = false;
        int rc;

        path[0] = '\0';
        spin_lock(&sus_path_lock);
        slot = NULL;
        list_for_each_entry(e, &sus_path_list, list) {
            if (!e->inode && e->pass != gen) {
                memcpy(path, e->path, e->path_len + 1);
                e->pass = gen;
                slot = e;
                break;
            }
        }
        spin_unlock(&sus_path_lock);
        if (!slot)
            break;              /* every pending rule was attempted */

        name[0] = '\0';

        WRITE_ONCE(sus_path_resolver, current);
        saved = sus_path_override_creds(&borrowed);
        rc = kern_path(path, LOOKUP_FOLLOW, &p);
        sus_path_revert_creds(saved, borrowed);
        WRITE_ONCE(sus_path_resolver, NULL);

        atomic_set(&sus_path_pend_last_rc, rc);
        if (!rc) {
            atomic_inc(&sus_path_pend_walks);
            inode = d_inode(p.dentry);
            if (inode) {
                strscpy(name, p.dentry->d_name.name, sizeof(name));
                /* Hold it before path_put() can evict it; published only afterwards. */
                ihold(inode);
            }
            path_put(&p);
        } else if (rc != atomic_read(&sus_path_pend_logged_rc)) {

            atomic_set(&sus_path_pend_logged_rc, rc);
            SUSFS_LOGI("sus_path: pending walk rc=%d (%d pending, pass %u)\n",
                    rc, atomic_read(&sus_path_n_pending), gen);
        }

        spin_lock(&sus_path_lock);
        slot = NULL;
        list_for_each_entry(e, &sus_path_list, list) {
            if (e->pass == gen && !e->inode && !strcmp(e->path, path)) {
                slot = e;
                break;
            }
        }
        if (slot && inode) {
            slot->dev = (u64)inode->i_sb->s_dev;
            slot->ino = (u64)inode->i_ino;
            strscpy(slot->name, name, sizeof(slot->name));
            slot->inode = inode;
            inode = NULL;               /* the table holds the reference now */
            atomic_dec(&sus_path_n_pending);
            resolved++;
            published = true;

            sus_path_relax_mode(slot);
        }
        spin_unlock(&sus_path_lock);

        if (inode) {
            iput(inode);                /* the rule is gone, or already resolved */
        } else if (!published && !rc) {
            atomic_inc(&sus_path_pend_lost);    /* walk ok, nothing to publish */
        }
    }

    if (resolved)
        SUSFS_LOGI("sus_path: resolved %d pending rule(s), %d still unresolved\n",
                resolved, atomic_read(&sus_path_n_pending));

    mutex_unlock(&sus_path_pending_lock);
    return resolved;
}

static void sus_path_pending_arm(void)
{
    if (!atomic_read(&sus_path_n_pending))
        return;

    sus_path_resolve_pending();
    if (!atomic_read(&sus_path_n_pending))
        return;

    atomic_set(&sus_path_pending_tries, 0);
    schedule_delayed_work(&sus_path_pending_wq, SUS_PATH_PENDING_RETRY_S * HZ);
}

static void sus_path_pending_work(struct work_struct *w)
{
    int resolved;

    atomic_inc(&sus_path_pend_ticks);
    resolved = sus_path_resolve_pending();

    if (!atomic_read(&sus_path_n_pending))
        return;                 /* every rule has its inode now */

    if (resolved > 0)
        atomic_set(&sus_path_pending_tries, 0);     /* progress: keep trying */

    if (atomic_inc_return(&sus_path_pending_tries) > SUS_PATH_PENDING_TRIES) {
        SUSFS_LOGI("sus_path: %d rule(s) still pending after %d retries (last walk rc=%d) - retry timer stops; they hide nothing until they resolve, the next add tries again\n",
                atomic_read(&sus_path_n_pending), SUS_PATH_PENDING_TRIES,
                atomic_read(&sus_path_pend_last_rc));
        return;
    }
    schedule_delayed_work(&sus_path_pending_wq, SUS_PATH_PENDING_RETRY_S * HZ);
}

static int sus_path_inode_getattr(const struct path *path);
static int sus_path_inode_permission(struct inode *inode, int mask);

#define LSM_HOOK_FN_TYPE(member) typeof(((union security_list_options *)0)->member)

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
#define SUS_LSM_PASS_ORIG(hook, member, ...)						\
	do {										\
		LSM_HOOK_FN_TYPE(member) __susfs_orig;				\
		/* Load-load fence before the read.  The switch that sent this call		\
		 * here is a plain store of key->func (the publish order in			\
		 * ksu_lsm_hook_insert_scall()), and on a weakly ordered CPU the load	\
		 * of original may be satisfied before the load of key->func that			\
		 * preceded it - which is how this reads NULL on an armed hook and drops	\
		 * SELinux's decision for that call.  The writer-side smp_wmb() closes	\
		 * the propagation half, this closes the reader half; it is one			\
		 * dmb ishld and only on the non-hidden path. */				\
		smp_rmb();								\
		__susfs_orig = (LSM_HOOK_FN_TYPE(member))READ_ONCE((hook).original);	\
		/* Through the trampoline, never directly: a checked indirect call into	\
		 * the kernel panics instead of failing (see SUS_LSM_ORIG_CALL above). */	\
		if (__susfs_orig)							\
			return sus_path_orig_##member(__susfs_orig, __VA_ARGS__);	\
	} while (0)
#else
#define SUS_LSM_PASS_ORIG(hook, member, ...) do { } while (0)
#endif

static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(inode_getattr),
					   typeof(&sus_path_inode_getattr)),
	      "inode_getattr hook signature mismatch");
static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(inode_permission),
					   typeof(&sus_path_inode_permission)),
	      "inode_permission hook signature mismatch");

static int sus_path_inode_unlink(struct inode *dir, struct dentry *dentry);
static int sus_path_inode_rmdir(struct inode *dir, struct dentry *dentry);
static int sus_path_inode_rename(struct inode *old_dir, struct dentry *old_dentry,
				 struct inode *new_dir, struct dentry *new_dentry);
static int sus_path_inode_link(struct dentry *old_dentry, struct inode *dir,
			       struct dentry *new_dentry);

static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(inode_unlink),
					   typeof(&sus_path_inode_unlink)),
	      "inode_unlink hook signature mismatch");
static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(inode_rmdir),
					   typeof(&sus_path_inode_rmdir)),
	      "inode_rmdir hook signature mismatch");
static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(inode_rename),
					   typeof(&sus_path_inode_rename)),
	      "inode_rename hook signature mismatch");
static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(inode_link),
					   typeof(&sus_path_inode_link)),
	      "inode_link hook signature mismatch");

static struct ksu_lsm_hook sus_path_unlink_hook =
	KSU_LSM_HOOK_INSERT(inode_unlink, (void *)sus_path_inode_unlink);

static struct ksu_lsm_hook sus_path_rmdir_hook =
	KSU_LSM_HOOK_INSERT(inode_rmdir, (void *)sus_path_inode_rmdir);

static struct ksu_lsm_hook sus_path_rename_hook =
	KSU_LSM_HOOK_INSERT(inode_rename, (void *)sus_path_inode_rename);

static struct ksu_lsm_hook sus_path_link_hook =
	KSU_LSM_HOOK_INSERT(inode_link, (void *)sus_path_inode_link);

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 3, 0)
#define SUS_XATTR_MNT_ID_DECL	struct mnt_idmap *idmap,
#define SUS_XATTR_MNT_ID_TYPE	struct mnt_idmap *,
#define SUS_XATTR_MNT_ID_ARG	idmap,
#elif LINUX_VERSION_CODE >= KERNEL_VERSION(5, 12, 0)
#define SUS_XATTR_MNT_ID_DECL	struct user_namespace *mnt_userns,
#define SUS_XATTR_MNT_ID_TYPE	struct user_namespace *,
#define SUS_XATTR_MNT_ID_ARG	mnt_userns,
#else	/* before idmapped mounts the hook never received an id mapping */
#define SUS_XATTR_MNT_ID_DECL
#define SUS_XATTR_MNT_ID_TYPE
#define SUS_XATTR_MNT_ID_ARG
#endif

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
#define SUS_SETATTR_MNT_ID_DECL	struct mnt_idmap *idmap,
#define SUS_SETATTR_MNT_ID_ARG	idmap,
#else
#define SUS_SETATTR_MNT_ID_DECL
#define SUS_SETATTR_MNT_ID_ARG
#endif

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
/* A hook that TAKEN OVER SELinux's slot still has to run SELinux's decision, which it does by
 * calling the saved original through `hook.original` (SUS_LSM_PASS_ORIG below).  That call
 * goes through these trampolines instead of being made at the call site, and they are
 * __nocfi, because an INSTRUMENTED indirect call into the kernel panics here rather than
 * failing: the type id this module expects and the one the kernel emitted for its own
 * function do not agree.  Measured on a 5.15 device - the first call through a
 * kallsyms-resolved pointer died with
 *
 *     Kernel panic - not syncing: CFI failure (target: kallsyms_on_each_symbol+0x0/0x1e4)
 *
 * `noinline` is not decoration either.  LTO treats the attribute as a property of the
 * function it was written on, so it inlines an unchecked call back into a caller that lacks
 * it and the check reappears THERE - which is how that panic ended up in
 * susfs_sus_mount_supercall() instead of in the function that made the call.
 *
 * One trampoline per hook member, because each has to be called through its own prototype
 * (and the two idmap arguments are version-dependent, hence the DECL/ARG macros); the macro
 * only saves repeating the cast and the two attributes.  tools/cfi_sites.py asserts on the
 * built .ko that no other function in this module carries a checked call. */
#define SUS_LSM_ORIG_CALL(member, ...)						\
	static __nocfi noinline int sus_path_orig_##member(			\
		LSM_HOOK_FN_TYPE(member) fn, __VA_ARGS__)

SUS_LSM_ORIG_CALL(inode_getattr, const struct path *path)
{
	return fn(path);
}

SUS_LSM_ORIG_CALL(inode_permission, struct inode *inode, int mask)
{
	return fn(inode, mask);
}

SUS_LSM_ORIG_CALL(inode_unlink, struct inode *dir, struct dentry *dentry)
{
	return fn(dir, dentry);
}

SUS_LSM_ORIG_CALL(inode_rmdir, struct inode *dir, struct dentry *dentry)
{
	return fn(dir, dentry);
}

SUS_LSM_ORIG_CALL(inode_rename, struct inode *old_dir, struct dentry *old_dentry,
		  struct inode *new_dir, struct dentry *new_dentry)
{
	return fn(old_dir, old_dentry, new_dir, new_dentry);
}

SUS_LSM_ORIG_CALL(inode_link, struct dentry *old_dentry, struct inode *dir,
		  struct dentry *new_dentry)
{
	return fn(old_dentry, dir, new_dentry);
}

SUS_LSM_ORIG_CALL(sb_statfs, struct dentry *dentry)
{
	return fn(dentry);
}

SUS_LSM_ORIG_CALL(inode_setattr, SUS_SETATTR_MNT_ID_DECL
		  struct dentry *dentry, struct iattr *attr)
{
	return fn(SUS_SETATTR_MNT_ID_ARG dentry, attr);
}

SUS_LSM_ORIG_CALL(inode_getxattr, struct dentry *dentry, const char *name)
{
	return fn(dentry, name);
}

SUS_LSM_ORIG_CALL(inode_listxattr, struct dentry *dentry)
{
	return fn(dentry);
}

SUS_LSM_ORIG_CALL(inode_setxattr, SUS_XATTR_MNT_ID_DECL
		  struct dentry *dentry, const char *name, const void *value,
		  size_t size, int flags)
{
	return fn(SUS_XATTR_MNT_ID_ARG dentry, name, value, size, flags);
}

SUS_LSM_ORIG_CALL(inode_removexattr, SUS_XATTR_MNT_ID_DECL
		  struct dentry *dentry, const char *name)
{
	return fn(SUS_XATTR_MNT_ID_ARG dentry, name);
}

SUS_LSM_ORIG_CALL(path_notify, const struct path *path, u64 mask,
		  unsigned int obj_type)
{
	return fn(path, mask, obj_type);
}
#endif	/* >= 6.12: the slot-takeover path is the only one that calls an original */

static int sus_path_sb_statfs(struct dentry *dentry);
static int sus_path_inode_setattr(SUS_SETATTR_MNT_ID_DECL
				  struct dentry *dentry, struct iattr *attr);
static int sus_path_inode_getxattr(struct dentry *dentry, const char *name);
static int sus_path_inode_listxattr(struct dentry *dentry);
static int sus_path_inode_setxattr(SUS_XATTR_MNT_ID_DECL
				   struct dentry *dentry, const char *name,
				   const void *value, size_t size, int flags);
static int sus_path_inode_removexattr(SUS_XATTR_MNT_ID_DECL
				      struct dentry *dentry, const char *name);
static int sus_path_path_notify(const struct path *path, u64 mask,
				unsigned int obj_type);

static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(sb_statfs),
					   typeof(&sus_path_sb_statfs)),
	      "sb_statfs hook signature mismatch");
static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(inode_setattr),
					   typeof(&sus_path_inode_setattr)),
	      "inode_setattr hook signature mismatch");
static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(inode_getxattr),
					   typeof(&sus_path_inode_getxattr)),
	      "inode_getxattr hook signature mismatch");
static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(inode_listxattr),
					   typeof(&sus_path_inode_listxattr)),
	      "inode_listxattr hook signature mismatch");
static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(inode_setxattr),
					   typeof(&sus_path_inode_setxattr)),
	      "inode_setxattr hook signature mismatch");
static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(inode_removexattr),
					   typeof(&sus_path_inode_removexattr)),
	      "inode_removexattr hook signature mismatch");
static_assert(__builtin_types_compatible_p(LSM_HOOK_FN_TYPE(path_notify),
					   typeof(&sus_path_path_notify)),
	      "path_notify hook signature mismatch");

static struct ksu_lsm_hook sus_path_statfs_hook =
	KSU_LSM_HOOK_INSERT(sb_statfs, (void *)sus_path_sb_statfs);

static struct ksu_lsm_hook sus_path_setattr_hook =
	KSU_LSM_HOOK_INSERT(inode_setattr, (void *)sus_path_inode_setattr);

static struct ksu_lsm_hook sus_path_getxattr_hook =
	KSU_LSM_HOOK_INSERT(inode_getxattr, (void *)sus_path_inode_getxattr);

static struct ksu_lsm_hook sus_path_listxattr_hook =
	KSU_LSM_HOOK_INSERT(inode_listxattr, (void *)sus_path_inode_listxattr);

static struct ksu_lsm_hook sus_path_setxattr_hook =
	KSU_LSM_HOOK_INSERT(inode_setxattr, (void *)sus_path_inode_setxattr);

static struct ksu_lsm_hook sus_path_removexattr_hook =
	KSU_LSM_HOOK_INSERT(inode_removexattr, (void *)sus_path_inode_removexattr);

static struct ksu_lsm_hook sus_path_notify_hook =
	KSU_LSM_HOOK_INSERT(path_notify, (void *)sus_path_path_notify);

static struct ksu_lsm_hook sus_path_getattr_hook =
	KSU_LSM_HOOK_INSERT(inode_getattr, (void *)sus_path_inode_getattr);

static struct ksu_lsm_hook sus_path_perm_hook =
	KSU_LSM_HOOK_INSERT(inode_permission, (void *)sus_path_inode_permission);

static atomic_t n_enoent_getattr = ATOMIC_INIT(0);
static atomic_t n_enoent_perm = ATOMIC_INIT(0);

static void sus_path_entry_set_path(struct sus_path_entry *e, const char *path)
{
    size_t n = strnlen(path, SUS_PATH_LEN - 1);

    while (n > 1 && path[n - 1] == '/')
        n--;
    memcpy(e->path, path, n);
    e->path[n] = '\0';
    e->path_len = (unsigned int)n;
}

static atomic_t n_identity_hits = ATOMIC_INIT(0);

static bool sus_path_inode_hidden(struct inode *inode)
{
    struct sus_path_entry *e;
    bool hidden = false, by_identity = false;
    u64 dev;

    if (!inode || !READ_ONCE(sus_path_count))
        return false;

    if (sus_path_is_resolver())
        return false;

    dev = (u64)inode->i_sb->s_dev;

    spin_lock(&sus_path_lock);
    list_for_each_entry(e, &sus_path_list, list) {
        /* Fast path: the exact object the rule resolved. */
        if (e->inode == inode) {
            if (sus_path_entry_gate_inode(e, inode)) {
                hidden = true;
                break;
            }
            continue;
        }

        if (!e->ino || e->ino != (u64)inode->i_ino)
            continue;
        if (e->dev == dev) {
            by_identity = true;
            if (sus_path_entry_gate_inode(e, inode)) {
                hidden = true;
                break;
            }
            continue;
        }
        /* Another instance of the same filesystem: control nodes only, see above. */
        if (e->self_protect && e->inode &&
            e->inode->i_sb->s_type == inode->i_sb->s_type) {
            by_identity = true;
            if (sus_path_entry_gate_inode(e, inode)) {
                hidden = true;
                break;
            }
        }
    }
    spin_unlock(&sus_path_lock);

    if (by_identity)
        atomic_inc(&n_identity_hits);

    return hidden;
}

static int sus_path_inode_getattr(const struct path *path)
{
    struct inode *inode;

    if (path && path->dentry) {
        inode = d_inode(path->dentry);
        if (sus_path_inode_hidden(inode)) {
            atomic_inc(&n_enoent_getattr);
            return -ENOENT;
        }
    }

    SUS_LSM_PASS_ORIG(sus_path_getattr_hook, inode_getattr, path);
    return 0;
}

static int sus_path_inode_permission(struct inode *inode, int mask)
{
    if (sus_path_inode_hidden(inode)) {
        atomic_inc(&n_enoent_perm);
        return -ENOENT;
    }

    SUS_LSM_PASS_ORIG(sus_path_perm_hook, inode_permission, inode, mask);
    return 0;
}

static atomic_t n_enoent_nameop = ATOMIC_INIT(0);

/* A negative dentry has no inode, which is exactly the "not hidden" answer. */
static bool sus_path_dentry_hidden(const struct dentry *dentry)
{
    struct inode *inode;

    if (!dentry)
        return false;
    inode = d_inode(dentry);
    return inode && sus_path_inode_hidden(inode);
}

static int sus_path_nameop_hit(void)
{
    atomic_inc(&n_enoent_nameop);
    return -ENOENT;
}

static int sus_path_inode_unlink(struct inode *dir, struct dentry *dentry)
{
    if (sus_path_dentry_hidden(dentry))
        return sus_path_nameop_hit();
    SUS_LSM_PASS_ORIG(sus_path_unlink_hook, inode_unlink, dir, dentry);
    return 0;
}

static int sus_path_inode_rmdir(struct inode *dir, struct dentry *dentry)
{
    if (sus_path_dentry_hidden(dentry))
        return sus_path_nameop_hit();
    SUS_LSM_PASS_ORIG(sus_path_rmdir_hook, inode_rmdir, dir, dentry);
    return 0;
}

static int sus_path_inode_rename(struct inode *old_dir, struct dentry *old_dentry,
				 struct inode *new_dir, struct dentry *new_dentry)
{

    if (sus_path_dentry_hidden(old_dentry) || sus_path_dentry_hidden(new_dentry))
        return sus_path_nameop_hit();
    SUS_LSM_PASS_ORIG(sus_path_rename_hook, inode_rename, old_dir, old_dentry,
                      new_dir, new_dentry);
    return 0;
}

static int sus_path_inode_link(struct dentry *old_dentry, struct inode *dir,
			       struct dentry *new_dentry)
{

    if (sus_path_dentry_hidden(old_dentry))
        return sus_path_nameop_hit();
    SUS_LSM_PASS_ORIG(sus_path_link_hook, inode_link, old_dentry, dir, new_dentry);
    return 0;
}

static atomic_t n_enoent_meta = ATOMIC_INIT(0);

static int sus_path_meta_hit(void)
{
    atomic_inc(&n_enoent_meta);
    return -ENOENT;
}

static int sus_path_sb_statfs(struct dentry *dentry)
{
    if (sus_path_dentry_hidden(dentry))
        return sus_path_meta_hit();
    SUS_LSM_PASS_ORIG(sus_path_statfs_hook, sb_statfs, dentry);
    return 0;
}

static int sus_path_inode_setattr(SUS_SETATTR_MNT_ID_DECL
				  struct dentry *dentry, struct iattr *attr)
{
    if (sus_path_dentry_hidden(dentry))
        return sus_path_meta_hit();
    SUS_LSM_PASS_ORIG(sus_path_setattr_hook, inode_setattr,
                      SUS_SETATTR_MNT_ID_ARG dentry, attr);
    return 0;
}

static int sus_path_inode_getxattr(struct dentry *dentry, const char *name)
{
    if (sus_path_dentry_hidden(dentry))
        return sus_path_meta_hit();
    SUS_LSM_PASS_ORIG(sus_path_getxattr_hook, inode_getxattr, dentry, name);
    return 0;
}

static int sus_path_inode_listxattr(struct dentry *dentry)
{
    if (sus_path_dentry_hidden(dentry))
        return sus_path_meta_hit();
    SUS_LSM_PASS_ORIG(sus_path_listxattr_hook, inode_listxattr, dentry);
    return 0;
}

static int sus_path_inode_setxattr(SUS_XATTR_MNT_ID_DECL
				   struct dentry *dentry, const char *name,
				   const void *value, size_t size, int flags)
{
    if (sus_path_dentry_hidden(dentry))
        return sus_path_meta_hit();
    SUS_LSM_PASS_ORIG(sus_path_setxattr_hook, inode_setxattr,
                      SUS_XATTR_MNT_ID_ARG dentry, name, value, size, flags);
    return 0;
}

static int sus_path_inode_removexattr(SUS_XATTR_MNT_ID_DECL
				      struct dentry *dentry, const char *name)
{
    if (sus_path_dentry_hidden(dentry))
        return sus_path_meta_hit();
    SUS_LSM_PASS_ORIG(sus_path_removexattr_hook, inode_removexattr,
                      SUS_XATTR_MNT_ID_ARG dentry, name);
    return 0;
}

static int sus_path_path_notify(const struct path *path, u64 mask, unsigned int obj_type)
{

    if (path && sus_path_dentry_hidden(path->dentry))
        return sus_path_meta_hit();
    SUS_LSM_PASS_ORIG(sus_path_notify_hook, path_notify, path, mask, obj_type);
    return 0;
}

static bool hooks_armed;

static int n_lsm_ext_fail;
static const char *first_lsm_ext_fail;

static DEFINE_MUTEX(sus_path_arm_lock);

struct sus_dirent64_compat {
    u32 d_ino;
    u32 d_off;
    unsigned short d_reclen;
    char d_name[];
};

enum {
    SUS_DIRENT_L64 = 0,     /* struct linux_dirent64      (native and AArch32 61/217) */
    SUS_DIRENT_COMPAT,      /* struct compat_linux_dirent (AArch32 141)              */
    SUS_DIRENT_N,
};

struct sus_dirent_layout {
    unsigned char id;
    unsigned char ino_size;     /* 8 native, 4 compat */
    unsigned char name_off;     /* offset of d_name */
    unsigned char reclen_off;   /* offset of d_reclen */
};

static const struct sus_dirent_layout sus_dirent_l64 = {
    .id = SUS_DIRENT_L64,
    .ino_size = 8,
    .name_off = offsetof(struct linux_dirent64, d_name),
    .reclen_off = offsetof(struct linux_dirent64, d_reclen),
};

static const struct sus_dirent_layout sus_dirent_compat = {
    .id = SUS_DIRENT_COMPAT,
    .ino_size = 4,
    .name_off = offsetof(struct sus_dirent64_compat, d_name),
    .reclen_off = offsetof(struct sus_dirent64_compat, d_reclen),
};

static atomic_t n_dirent_calls[SUS_DIRENT_N];

static atomic_t n_dirent_no_filter[SUS_DIRENT_N];   /* sus_path_filter() found no buffer/knows the layout not */
static atomic_t n_dirent_syscall_bad[SUS_DIRENT_N]; /* return <= 0: error, or an empty listing  */
static atomic_t n_dirent_buf_null[SUS_DIRENT_N];    /* NULL user buffer: nothing to rewrite      */
static atomic_t n_dirent_no_rule[SUS_DIRENT_N];     /* count==0 and hide_name unset: nothing to hide */

static const char *sus_path_dirent_abi_name(int lay_id)
{
    return lay_id == SUS_DIRENT_COMPAT ? "getdents (AArch32 141)"
                                       : "getdents64 (native 61 + AArch32 217)";
}

static long sus_path_filter(unsigned long buf, long count,
                            const struct sus_dirent_layout *lay);

/* Which dirent layout this syscall denotes for a task running the given ABI, or -1 for "not a
 * listing call".  The ABI gate is the whole point of this function: matching the bare number
 * made every native getpriority (141) look like an AArch32 getdents, so the module took the
 * nice value (1..40) for a byte count and the `who` tid for a user buffer it then failed to
 * read - a warning at the ratelimit on a completely unrelated syscall. */
int sus_path_dirent_layout_id(long syscall_nr, bool compat)
{
    if (compat) {
        if (syscall_nr == SUS_NR_GETDENTS_COMPAT)
            return SUS_DIRENT_COMPAT;
        if (syscall_nr == SUS_NR_GETDENTS64_COMPAT)
            return SUS_DIRENT_L64;
        return -1;
    }
    return syscall_nr == __NR_getdents64 ? SUS_DIRENT_L64 : -1;
}

/* lay_id comes from sus_path_dirent_layout_id(); buf/ret are only read for a listing call. */
long sus_path_dirent_filter(int lay_id, unsigned long buf, long ret)
{
    /* The counters are indexed by this id, so an id that did not come from the classifier is
     * answered with "nothing filtered" instead of being used as an index. */
    if (lay_id < 0 || lay_id >= SUS_DIRENT_N)
        return ret;

    if (ret <= 0) {
        atomic_inc(&n_dirent_syscall_bad[lay_id]);
        return ret;
    }
    return sus_path_filter(buf, ret, lay_id == SUS_DIRENT_COMPAT ? &sus_dirent_compat
                                                                 : &sus_dirent_l64);
}

int sus_path_dirent_stat_line(char *buf, size_t size)
{
    return scnprintf(buf, size,
        "  dirent (via the sys_exit tracepoint): l64=%d compat=%d | no-filter(l64=%d compat=%d) "
        "| bad-ret(l64=%d compat=%d) null-buf(l64=%d compat=%d) "
        "no-rule(l64=%d compat=%d) rewrite-fail=%d all-hidden=%d pending=%d\n",
        atomic_read(&n_dirent_calls[SUS_DIRENT_L64]),
        atomic_read(&n_dirent_calls[SUS_DIRENT_COMPAT]),
        atomic_read(&n_dirent_no_filter[SUS_DIRENT_L64]),
        atomic_read(&n_dirent_no_filter[SUS_DIRENT_COMPAT]),
        atomic_read(&n_dirent_syscall_bad[SUS_DIRENT_L64]),
        atomic_read(&n_dirent_syscall_bad[SUS_DIRENT_COMPAT]),
        atomic_read(&n_dirent_buf_null[SUS_DIRENT_L64]),
        atomic_read(&n_dirent_buf_null[SUS_DIRENT_COMPAT]),
        atomic_read(&n_dirent_no_rule[SUS_DIRENT_L64]),
        atomic_read(&n_dirent_no_rule[SUS_DIRENT_COMPAT]),
        atomic_read(&n_dirent_rewrite_fail),
        atomic_read(&n_dirent_all_hidden),
        atomic_read(&sus_path_n_pending));
}

static void sus_path_hooks_arm(void)
{
    mutex_lock(&sus_path_arm_lock);
    if (hooks_armed || !READ_ONCE(sus_path_count)) {
        mutex_unlock(&sus_path_arm_lock);
        return;
    }

    hooks_armed = true;

    if (no_extra)
        pr_warn("sus_path: no_extra - dirent filter off\n");

    SUSFS_LOGI("sus_path: hooks armed (LSM + dirent rewrite on the shared sys_exit tracepoint)\n");
    mutex_unlock(&sus_path_arm_lock);
}

static long sus_path_filter(unsigned long buf, long count,
                            const struct sus_dirent_layout *lay)
{
    long offset = 0;        /* read position in the caller's chain */
    long written = 0;       /* bytes of the compacted chain already handed back */
    unsigned short head_reclen = 0;     /* first record's length, for the placeholder */
    bool failed = false;
    char *tmp;
    int id = sus_dirent_l64.id;         /* which ABI's counters to move */

    if (lay == &sus_dirent_compat)
        id = sus_dirent_compat.id;

    atomic_inc(&n_dirent_calls[id]);

    if (!buf) {
        atomic_inc(&n_dirent_buf_null[id]);
        return count;
    }

    if (!READ_ONCE(sus_path_count) && !hide_name[0]) {
        atomic_inc(&n_dirent_no_rule[id]);
        return count;
    }

    spin_lock(&sus_path_buf_lock);

    pagefault_disable();

    tmp = dirent_tmp;
    if (!tmp) {
        pagefault_enable();
        spin_unlock(&sus_path_buf_lock);
        atomic_inc(&n_dirent_no_filter[id]);
        return count;
    }

    while (offset < count) {
        unsigned long long ino = 0;
        unsigned short reclen;
        char name[NAME_MAX + 1];
        long nlen;
        bool hide;

        if (copy_from_user(&reclen, (void __user *)(buf + offset + lay->reclen_off),
                           sizeof(reclen))) {
            failed = true;
            break;
        }

        if (reclen < lay->name_off + 1 ||
            offset + reclen > count ||
            reclen > DIRENT_BUF_SIZE) {
            failed = true;
            break;
        }

        if (lay->ino_size == 8) {
            if (copy_from_user(&ino, (void __user *)(buf + offset), sizeof(u64))) {
                failed = true;
                break;
            }
        } else {
            u32 ino32;

            if (copy_from_user(&ino32, (void __user *)(buf + offset), sizeof(ino32))) {
                failed = true;
                break;
            }
            ino = ino32;
        }

        nlen = strnlen_user((void __user *)(buf + offset + lay->name_off),
                            sizeof(name) - 1);
        if (nlen == 0) {            /* no readable NUL in the name field */
            failed = true;
            break;
        }
        if (nlen >= sizeof(name))   /* longer than NAME_MAX: cannot match */
            nlen = sizeof(name) - 1;
        if (nlen > reclen - lay->name_off) {
            failed = true;
            break;
        }
        if (copy_from_user(name, (void __user *)(buf + offset + lay->name_off), nlen)) {
            failed = true;
            break;
        }
        name[nlen] = 0;
        if (!head_reclen)
            head_reclen = reclen;

        hide = sus_path_is_hidden((u64)ino, name);

        if (hide) {

            offset += reclen;
            continue;
        }

        if (written != offset) {
            if (copy_from_user(tmp, (void __user *)(buf + offset), reclen)) {
                failed = true;
                break;
            }
            if (copy_to_user((void __user *)(buf + written), tmp, reclen)) {
                failed = true;
                break;
            }
        }
        written += reclen;
        offset += reclen;
    }

    pagefault_enable();
    spin_unlock(&sus_path_buf_lock);

    if (failed) {
        atomic_inc(&n_dirent_rewrite_fail);
        pr_warn_ratelimited("sus_path: dirent rewrite stopped at %ld/%ld bytes (returned %ld)\n",
                            offset, count, written ? written : count);
        if (!written)
            return count;       /* nothing was written back: claim no filtering */
    }

    if (!failed && count > 0 && written == 0) {
        char zero_ino[8] = {0};
        char nul = '\0';

        if (head_reclen >= lay->name_off + 1 && head_reclen <= count &&
            !copy_to_user((void __user *)buf, zero_ino, lay->ino_size) &&
            !copy_to_user((void __user *)(buf + lay->name_off), &nul, 1)) {
            atomic_inc(&n_dirent_all_hidden);
            return head_reclen;
        }

        atomic_inc(&n_dirent_rewrite_fail);
        return count;
    }

    return written;
}

#define SUS_PATH_LIST_SLACK 400		/* longest line below (two names, 2x20 digits) */
static int sus_path_list_puts(char *buf, int n, bool *trunc, const char *fmt, ...)
{
    va_list args;
    int room, written;

    if (n < 0 || n >= (int)PAGE_SIZE - 1) {
        *trunc = true;
        return n;
    }
    room = (int)PAGE_SIZE - n;
    va_start(args, fmt);
    written = vsnprintf(buf + n, room, fmt, args);
    va_end(args);
    if (written >= room) {
        /* vsnprintf reports what it WOULD have written; room-1 + terminator fit. */
        *trunc = true;
        return (int)PAGE_SIZE - 1;
    }
    return n + written;
}

int sus_path_del_path(const char *path)
{
    struct sus_path_entry *e, *tmp;
    LIST_HEAD(doomed);
    char want[SUS_PATH_LEN];
    int removed = 0;
    int i;

    if (!path || !*path)
        return 0;

    strscpy(want, path, sizeof(want));
    for (i = (int)strlen(want); i > 1 && want[i - 1] == '/'; i--)
        want[i - 1] = '\0';

    spin_lock(&sus_path_lock);
    list_for_each_entry_safe(e, tmp, &sus_path_list, list) {
        if (strcmp(e->path, want))
            continue;
        list_del(&e->list);
        list_add(&e->list, &doomed);
        sus_path_count--;
        removed++;
    }
    spin_unlock(&sus_path_lock);

    list_for_each_entry_safe(e, tmp, &doomed, list) {
        list_del(&e->list);
        if (!e->inode)
            atomic_dec(&sus_path_n_pending);
        sus_path_restore_mode(e);
        if (e->inode)
            iput(e->inode);
        kfree(e);
    }
    if (removed)
        SUSFS_LOGI("sus_path: removed %d rule(s) for %s, %d left\n", removed, want,
                sus_path_count);
    return removed;
}

static bool sus_path_path_is_ours(const char *path)
{
    struct sus_path_entry *e;
    bool ours = false;

    spin_lock(&sus_path_lock);
    list_for_each_entry(e, &sus_path_list, list) {
        if (e->self_protect && !strcmp(e->path, path)) {
            ours = true;
            break;
        }
    }
    spin_unlock(&sus_path_lock);
    return ours;
}

static int sus_path_command(const char *val, int *removed_out)
{
    struct sus_path_entry *e, *tmp;
    LIST_HEAD(doomed);
    char cmd[SUS_PATH_LEN + 16];
    const char *arg;
    int i, removed = 0;

    strscpy(cmd, val, sizeof(cmd));
    /* A shell `echo` leaves a newline behind; trim it (and trailing spaces). */
    for (i = (int)strlen(cmd) - 1; i >= 0 && (cmd[i] == '\n' || cmd[i] == '\r' || cmd[i] == ' '); i--)
        cmd[i] = '\0';

    if (!strcmp(cmd, "clear")) {
        spin_lock(&sus_path_lock);
        list_for_each_entry_safe(e, tmp, &sus_path_list, list) {
            if (e->self_protect)
                continue;	/* ours: see the note above */
            list_del(&e->list);
            list_add(&e->list, &doomed);
            sus_path_count--;
            removed++;
        }
        spin_unlock(&sus_path_lock);
    } else if (!strncmp(cmd, "add ", 4) || !strncmp(cmd, "del ", 4)) {
        bool adding = (cmd[0] == 'a');

        arg = cmd + 4;
        while (*arg == ' ')
            arg++;
        if (!*arg)
            return -EINVAL;

        {
            size_t alen = strlen(arg);

            while (alen > 1 && arg[alen - 1] == '/')
                ((char *)arg)[--alen] = '\0';
        }
        if (!adding && sus_path_path_is_ours(arg))
            return -EPERM;
        if (adding) {
            int rc = sus_path_add_hidden(arg);

            if (rc)
                return rc;
        } else {
            removed = sus_path_del_path(arg);
        }
        SUSFS_LOGI("sus_path: %s %s, %d rule(s) removed, %d left\n",
                adding ? "add" : "del", arg, removed, sus_path_count);
    } else {
        return -EINVAL;
    }

    /* Outside the lock: restore_mode() writes i_mode and iput() can sleep and evict. */
    list_for_each_entry_safe(e, tmp, &doomed, list) {
        list_del(&e->list);
        if (!e->inode)
            atomic_dec(&sus_path_n_pending);
        sus_path_restore_mode(e);
        if (e->inode)
            iput(e->inode);
        kfree(e);
    }
    SUSFS_LOGI("sus_path: command written, %d rule(s) removed, %d left\n",
            removed, sus_path_count);
    if (removed_out)
        *removed_out = removed;
    return 0;
}

static int sus_path_store_list(const char *val, const struct kernel_param *kp)
{
    return sus_path_command(val, NULL);
}

static int sus_path_format_list(char *buf, size_t size)
{
    struct sus_path_entry *e;
    bool trunc = false;
    int n = 0;

    n = sus_path_list_puts(buf, n, &trunc,
                   "hide_from_apps=%d  enoent: getattr=%d perm=%d nameop=%d meta=%d\n",
                   hide_from_apps, atomic_read(&n_enoent_getattr),
                   atomic_read(&n_enoent_perm), atomic_read(&n_enoent_nameop),
                   atomic_read(&n_enoent_meta));

    n = sus_path_list_puts(buf, n, &trunc,
                   "dirent: pending=%d (counters: /proc/susfs_kstat)\n",
                   atomic_read(&sus_path_n_pending));
    if (n_lsm_ext_fail)
        n = sus_path_list_puts(buf, n, &trunc,
                       "lsm: %d secondary hook(s) FAILED (first: %s) - that operation is not covered\n",
                       n_lsm_ext_fail, first_lsm_ext_fail);

    if (atomic_read(&n_identity_hits))
        n = sus_path_list_puts(buf, n, &trunc,
                       "identity: %d hit(s) where the inode pointer did not match and (dev,ino) or (fs type,ino) answered instead\n",
                       atomic_read(&n_identity_hits));

    n = sus_path_list_puts(buf, n, &trunc,
                   "pend: passes=%d ticks=%d walks=%d lost=%d last-rc=%d caller-cred=%d\n",
                   atomic_read(&sus_path_pend_passes),
                   atomic_read(&sus_path_pend_ticks),
                   atomic_read(&sus_path_pend_walks),
                   atomic_read(&sus_path_pend_lost),
                   atomic_read(&sus_path_pend_last_rc),
                   (int)(sus_path_pending_cred != NULL));

    spin_lock(&sus_path_lock);
    list_for_each_entry(e, &sus_path_list, list) {
        if (n > (int)PAGE_SIZE - SUS_PATH_LIST_SLACK) {
            trunc = true;
            break;
        }
        n = sus_path_list_puts(buf, n, &trunc,
                       "path=%s  dev=%llu ino=%llu name=%s%s%s\n",
                       e->path[0] ? e->path : "(?)", e->dev, e->ino, e->name,
                       e->self_protect ? "  [ours: clear/del refuse it]" : "",
                       e->inode ? "" : "  (pending: no inode yet)");
    }
    spin_unlock(&sus_path_lock);

    if (!sus_path_count)
        n = sus_path_list_puts(buf, n, &trunc, "(no paths registered)\n");
    if (trunc)
        n = sus_path_list_puts(buf, n, &trunc,
                       "(truncated: the table holds more rules than one page; the rules are intact)\n");
    return n < (int)size ? n : (int)size - 1;
}

static int sus_path_show_list(char *buf, const struct kernel_param *kp)
{
    return sus_path_format_list(buf, PAGE_SIZE);
}

static struct proc_dir_entry *sus_path_node_entry;

static int sus_path_proc_show(struct seq_file *m, void *v)
{
    char *buf = kvmalloc(PAGE_SIZE, GFP_KERNEL);
    int n;

    if (!buf)
        return -ENOMEM;
    n = sus_path_format_list(buf, PAGE_SIZE);
    if (n > 0)
        seq_write(m, buf, (size_t)n);
    kvfree(buf);
    return 0;
}

static int sus_path_proc_open(struct inode *inode, struct file *file)
{

    if (current_uid().val != 0)
        return -ENOENT;
    return single_open(file, sus_path_proc_show, NULL);
}

static ssize_t sus_path_proc_write(struct file *file, const char __user *buf,
                                   size_t len, loff_t *off)
{
    char cmd[SUS_PATH_LEN + 16];
    int rc;

    if (current_uid().val != 0)
        return -ENOENT;
    if (len == 0)
        return 0;
    if (len >= sizeof(cmd))
        return -EINVAL;
    if (copy_from_user(cmd, buf, len))
        return -EFAULT;
    cmd[len] = '\0';

    rc = sus_path_command(cmd, NULL);
    if (rc)
        return rc;
    return len;	/* success reports the count, like every other node */
}

static const struct proc_ops sus_path_proc_ops = {
    .proc_open = sus_path_proc_open,
    .proc_read = seq_read,
    .proc_write = sus_path_proc_write,
    .proc_lseek = seq_lseek,
    .proc_release = single_release,
};

static const struct kernel_param_ops sus_path_list_ops = {
    .get = sus_path_show_list,
    .set = sus_path_store_list,
};

module_param_cb(hide_list, &sus_path_list_ops, NULL, 0600);

static char sus_path_probe_report[640];

static int sus_path_probe_set(const char *val, const struct kernel_param *kp)
{
    struct sus_path_entry *e;
    struct path p;
    struct inode *inode;
    char path[SUS_PATH_LEN];
    int i, rc, n, room;

    strscpy(path, val, sizeof(path));
    /* A shell `echo` leaves a newline behind; trim it (and trailing spaces). */
    for (i = (int)strlen(path) - 1; i >= 0 && (path[i] == '\n' || path[i] == '\r' || path[i] == ' '); i--)
        path[i] = '\0';
    if (!path[0])
        return -EINVAL;

    rc = kern_path(path, LOOKUP_FOLLOW, &p);
    if (rc) {
        scnprintf(sus_path_probe_report, sizeof(sus_path_probe_report),
              "path=%s: kern_path failed rc=%d\n", path, rc);
        return 0;
    }
    inode = d_inode(p.dentry);
    if (!inode) {
        path_put(&p);
        scnprintf(sus_path_probe_report, sizeof(sus_path_probe_report),
              "path=%s: no inode (negative dentry)\n", path);
        return 0;
    }

    n = scnprintf(sus_path_probe_report, sizeof(sus_path_probe_report),
              "path=%s\n  resolved: inode=%px dev=%llu ino=%llu uid=%u in_hidden_set=%d\n",
              path, inode, (unsigned long long)inode->i_sb->s_dev,
              (unsigned long long)inode->i_ino, current_uid().val,
              (int)sus_path_inode_hidden(inode));

    spin_lock(&sus_path_lock);
    list_for_each_entry(e, &sus_path_list, list) {
        if (e->dev != (u64)inode->i_sb->s_dev || e->ino != (u64)inode->i_ino)
            continue;
        room = (int)sizeof(sus_path_probe_report) - n;
        if (room < 200)
            break;
        i = scnprintf(sus_path_probe_report + n, room,
                  "  rule: inode=%px name=%s self_protect=%d ptr_equal=%d gate_inode=%d gate_any=%d\n",
                  e->inode, e->name, (int)e->self_protect,
                  (int)(e->inode == inode), (int)sus_path_entry_gate_inode(e, inode),
                  (int)sus_path_entry_gate_any(e));
        if (i >= room)
            break;
        n += i;
    }
    spin_unlock(&sus_path_lock);
    path_put(&p);
    return 0;
}

static int sus_path_probe_get(char *buf, const struct kernel_param *kp)
{
    return scnprintf(buf, PAGE_SIZE, "%s",
             sus_path_probe_report[0] ? sus_path_probe_report : "(no path probed yet)\n");
}

static const struct kernel_param_ops sus_path_probe_ops = {
    .get = sus_path_probe_get,
    .set = sus_path_probe_set,
};
module_param_cb(sus_path_probe, &sus_path_probe_ops, NULL, 0600);

static int sus_path_add_hidden_ex(const char *path, bool self_protect)
{
	struct path p;
	struct inode *inode;
	struct sus_path_entry *e;
	int rc;

	rc = kern_path(path, LOOKUP_FOLLOW, &p);
	if (rc)
		return rc;

	inode = d_inode(p.dentry);
	if (!inode) {
		path_put(&p);
		return -ENOENT;
	}

	e = kzalloc(sizeof(*e), GFP_KERNEL);
	if (!e) {
		path_put(&p);
		return -ENOMEM;
	}

	e->dev = (u64)inode->i_sb->s_dev;
	e->ino = (u64)inode->i_ino;
	e->inode = inode;
	e->pass = 0;
	e->self_protect = self_protect;
	ihold(inode);
	strscpy(e->name, p.dentry->d_name.name, sizeof(e->name));
	sus_path_entry_set_path(e, path);
	INIT_LIST_HEAD(&e->list);
	path_put(&p);

	spin_lock(&sus_path_lock);
	{
		struct sus_path_entry *cur;

		list_for_each_entry(cur, &sus_path_list, list) {
			if (cur->inode == inode) {
				spin_unlock(&sus_path_lock);
				iput(e->inode);
				kfree(e);
				return 0;	/* already hidden */
			}
		}
	}
	if (sus_path_count >= SUS_PATH_MAX_ENTRIES) {
		spin_unlock(&sus_path_lock);
		iput(e->inode);
		kfree(e);
		return -ENOSPC;
	}
	list_add_tail(&e->list, &sus_path_list);
	sus_path_count++;
	sus_path_relax_mode(e);
	spin_unlock(&sus_path_lock);

	SUSFS_LOGI("sus_path: hidden (built-in) '%s'%s\n", path,
		self_protect ? " (self-protected: hidden from every non-root caller)" : "");
	sus_path_hooks_arm();
	return 0;
}

int sus_path_add_self_hidden(const char *path)
{
	return sus_path_add_hidden_ex(path, true);
}

int sus_path_add_hidden(const char *path)
{
	return sus_path_add_hidden_ex(path, false);
}

bool sus_path_lsm_active(void)
{
	return sus_path_getattr_hook.entry && sus_path_perm_hook.entry;
}

int sus_path_init(void)
{
    int rc;

    dirent_tmp = kvmalloc(DIRENT_BUF_SIZE, GFP_KERNEL);
    if (!dirent_tmp)
        pr_warn("sus_path: dirent scratch buffer unavailable, listings will not be filtered\n");

    SUSFS_LOGI("sus_path: dirent rewrite rides the shared sys_exit tracepoint (no probe of its own)\n");

    if (no_extra) {
        SUSFS_LOGI("sus_path: no_extra=1 - the LSM layer and the dirent filter are OFF (isolation test)\n");
        return 0;
    }

    rc = ksu_register_lsm_hook(&sus_path_getattr_hook);
    if (rc) {
        pr_err("sus_path: getattr hook failed %d - nothing would be hidden, refusing to load\n", rc);

        kvfree(dirent_tmp);
        dirent_tmp = NULL;
        return rc;
    }
    SUSFS_LOGI("sus_path: getattr hook inserted ahead of the chain (node %px)\n",
            (void *)sus_path_getattr_hook.entry);

    rc = ksu_register_lsm_hook(&sus_path_perm_hook);
    if (rc) {
        pr_err("sus_path: perm hook failed %d - nothing would be hidden, refusing to load\n", rc);
        ksu_unregister_lsm_hook(&sus_path_getattr_hook);
        kvfree(dirent_tmp);
        dirent_tmp = NULL;
        return rc;
    }
    SUSFS_LOGI("sus_path: perm hook inserted ahead of the chain (node %px)\n",
            (void *)sus_path_perm_hook.entry);

    {
        struct ksu_lsm_hook *extra[] = {
            &sus_path_unlink_hook, &sus_path_rmdir_hook,
            &sus_path_rename_hook, &sus_path_link_hook,
            &sus_path_statfs_hook, &sus_path_setattr_hook,
            &sus_path_getxattr_hook, &sus_path_listxattr_hook,
            &sus_path_setxattr_hook, &sus_path_removexattr_hook,
            &sus_path_notify_hook,
        };
        int i;

        for (i = 0; i < (int)ARRAY_SIZE(extra); i++) {
            rc = ksu_register_lsm_hook(extra[i]);
            if (rc) {

                if (!n_lsm_ext_fail)
                    first_lsm_ext_fail = extra[i]->head_name;
                n_lsm_ext_fail++;
                pr_warn("sus_path: %s hook failed %d - that operation will not be covered\n",
                        extra[i]->head_name, rc);
            } else {
                SUSFS_LOGI("sus_path: %s hook inserted ahead of the chain (node %px)\n",
                        extra[i]->head_name, (void *)extra[i]->entry);
            }
        }
        if (n_lsm_ext_fail)
            pr_warn("sus_path: %d/%d secondary hooks failed (first: %s)\n",
                    n_lsm_ext_fail, (int)ARRAY_SIZE(extra), first_lsm_ext_fail);
    }

    if (susfs_control_node_allowed()) {
        sus_path_node_entry = proc_create("susfs_path", 0777, NULL, &sus_path_proc_ops);
        if (!sus_path_node_entry)
            pr_warn("sus_path: proc_create(susfs_path) failed - the listing stays reachable through the hide_list parameter\n");
    } else {
        SUSFS_LOGI("sus_path: /proc/susfs_path not created (expose_proc=%d lsm=%d)\n",
                (int)susfs_expose_proc, (int)sus_path_lsm_active());
    }
    return 0;
}

void sus_path_exit(void)
{
    struct sus_path_entry *e, *tmp;
    LIST_HEAD(doomed);

    if (sus_path_node_entry) {
        proc_remove(sus_path_node_entry);
        sus_path_node_entry = NULL;
    }

    cancel_delayed_work_sync(&sus_path_pending_wq);
    mutex_lock(&sus_path_pending_lock);
    mutex_unlock(&sus_path_pending_lock);
    /* No walk can be in flight now, so the borrowed creds are ours to release. */
    sus_path_drop_caller_cred();
    if (sus_path_perm_hook.entry)
        ksu_unregister_lsm_hook(&sus_path_perm_hook);
    {
        struct ksu_lsm_hook *extra[] = {
            &sus_path_unlink_hook, &sus_path_rmdir_hook,
            &sus_path_rename_hook, &sus_path_link_hook,
            &sus_path_statfs_hook, &sus_path_setattr_hook,
            &sus_path_getxattr_hook, &sus_path_listxattr_hook,
            &sus_path_setxattr_hook, &sus_path_removexattr_hook,
            &sus_path_notify_hook,
        };
        int i;

        for (i = 0; i < (int)ARRAY_SIZE(extra); i++) {
            if (extra[i]->entry)
                ksu_unregister_lsm_hook(extra[i]);
        }
    }
    if (sus_path_getattr_hook.entry)
        ksu_unregister_lsm_hook(&sus_path_getattr_hook);

    kvfree(dirent_tmp);
    dirent_tmp = NULL;

    spin_lock(&sus_path_lock);
    list_splice_init(&sus_path_list, &doomed);
    sus_path_count = 0;
    atomic_set(&sus_path_n_pending, 0);
    spin_unlock(&sus_path_lock);

    list_for_each_entry_safe(e, tmp, &doomed, list) {
        list_del(&e->list);
        sus_path_restore_mode(e);
        if (e->inode)
            iput(e->inode);
        kfree(e);
    }
}

void sus_path_supercall(unsigned int cmd, void __user **arg)
{
    struct st_susfs_sus_path info = {0};
    struct sus_path_entry *e;
    struct path path = {0};
    struct inode *inode = NULL;
    bool pending_ok = (cmd == CMD_SUSFS_ADD_SUS_PATH_LOOP);
    u64 dev = 0;
    u64 ino = 0;
    int rc;

    if (copy_from_user(&info, (void __user *)*arg, sizeof(info))) {
        info.err = -EFAULT;
        goto out;
    }

    if (!info.target_pathname[0]) {
        info.err = -EINVAL;
        goto out;
    }

    if (!susfs_abi_path_ok(info.target_pathname, sizeof(info.target_pathname))) {
        info.err = -ENAMETOOLONG;
        goto out;
    }

    rc = kern_path(info.target_pathname, LOOKUP_FOLLOW, &path);
    if (!rc) {
        inode = d_inode(path.dentry);
        if (!inode) {
            path_put(&path);
            rc = -ENOENT;
        }
    }
    if (rc && rc != -ENOENT) {
        pr_warn("sus_path: failed opening '%s' (%d)\n", info.target_pathname, rc);
        info.err = rc;
        goto out;
    }

    if (rc == -ENOENT && !pending_ok) {
        SUSFS_LOGI("sus_path: '%s' does not exist and this is ADD_SUS_PATH (not _LOOP): reporting -ENOENT like upstream\n",
                info.target_pathname);
        info.err = -ENOENT;
        goto out;
    }

    e = kzalloc(sizeof(*e), GFP_KERNEL);
    if (!e) {
        if (inode)
            path_put(&path);
        info.err = -ENOMEM;
        goto out;
    }

    e->dev = 0;
    e->ino = 0;
    e->inode = NULL;
    e->pass = 0;
    e->name[0] = '\0';

    if (inode) {
        dev = (u64)inode->i_sb->s_dev;
        ino = (u64)inode->i_ino;
        e->dev = dev;
        e->ino = ino;
        e->inode = inode;

        ihold(inode);
        strscpy(e->name, path.dentry->d_name.name, sizeof(e->name));
    }
    sus_path_entry_set_path(e, info.target_pathname);
    if (!inode)

        sus_path_basename(e->path, e->name, sizeof(e->name));
    INIT_LIST_HEAD(&e->list);
    if (inode)
        path_put(&path);

    spin_lock(&sus_path_lock);
    if (sus_path_count >= SUS_PATH_MAX_ENTRIES) {
        spin_unlock(&sus_path_lock);
        if (e->inode)
            iput(e->inode);
        kfree(e);
        info.err = -ENOSPC;
        goto out;
    }
    {
        struct sus_path_entry *cur;

        list_for_each_entry(cur, &sus_path_list, list) {

            if ((inode && cur->inode == inode) ||
                (!inode && !cur->inode && !strcmp(cur->path, e->path))) {
                spin_unlock(&sus_path_lock);
                if (e->inode)
                    iput(e->inode);
                kfree(e);
                info.err = 0;   /* already registered, upstream is idempotent */
                goto out;
            }

            if (inode && !cur->inode && !strcmp(cur->path, e->path)) {
                cur->dev = dev;
                cur->ino = ino;
                strscpy(cur->name, e->name, sizeof(cur->name));
                cur->inode = e->inode;      /* the reference moves over */
                e->inode = NULL;
                atomic_dec(&sus_path_n_pending);
                sus_path_relax_mode(cur);   /* it was pending, so it never ran */
                spin_unlock(&sus_path_lock);
                kfree(e);
                info.err = 0;
                SUSFS_LOGI("sus_path: hide '%s' (pending rule completed by this add, dev=%llu ino=%llu)\n",
                        info.target_pathname, dev, ino);
                goto out;
            }
        }
    }
    list_add_tail(&e->list, &sus_path_list);
    sus_path_count++;
    if (!inode)
        atomic_inc(&sus_path_n_pending);
    else
        sus_path_relax_mode(e);
    spin_unlock(&sus_path_lock);

    if (inode && !ino) {

        pr_warn("sus_path: '%s' reports ino 0 - hidden by inode, but a directory listing cannot be filtered for it\n",
                info.target_pathname);
    }

    if (!dirent_tmp) {

        dirent_tmp = kvmalloc(DIRENT_BUF_SIZE, GFP_KERNEL);
        if (!dirent_tmp)
            pr_warn("sus_path: dirent scratch buffer still unavailable, listing for '%s' stays unfiltered\n",
                    info.target_pathname);
    }

    sus_path_hooks_arm();

    if (!inode) {
        SUSFS_LOGI("sus_path: hide '%s' (pending: the path does not exist yet - it is hidden once the background walk resolves its inode)\n",
                info.target_pathname);

        sus_path_save_caller_cred();

        sus_path_pending_arm();
    } else {
        SUSFS_LOGI("sus_path: hide '%s' (dev=%llu ino=%llu)\n",
                info.target_pathname, dev, ino);
    }

    info.err = 0;
out:
    /* upstream writes back only ->err for input-type commands */
    if (copy_to_user(&((struct st_susfs_sus_path __user *)*arg)->err,
                     &info.err, sizeof(info.err)))
        pr_warn("sus_path supercall copy_to_user failed\n");
}
