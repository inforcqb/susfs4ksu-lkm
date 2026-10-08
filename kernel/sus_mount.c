// SPDX-License-Identifier: GPL-2.0

#include <linux/module.h>
#include <linux/kprobes.h>
#include <linux/fs.h>
#include <linux/seq_file.h>
#include <linux/stat.h>     /* struct statx (stx_mnt_id) */
#include <linux/uaccess.h>
#include <linux/sched.h>
#include <linux/cred.h>
#include <linux/nsproxy.h>
#include <linux/percpu.h>
#include <linux/rcupdate.h>
#include <linux/spinlock.h>
#include <linux/slab.h>
#include <linux/mm.h>		/* kvmalloc()/kvfree() for the keep-list staging buffers */
#include <linux/string.h>
#include <linux/list.h>
#include <linux/idr.h>      /* struct ida + ida_alloc_range()/ida_free() prototypes */
#include <linux/err.h>
#include <linux/errno.h>    /* -ENOSYS/-ENOENT/-ENOMEM used by the scan result */
#include <linux/dcache.h>   /* d_path() - called through a resolved symbol */
#include <linux/limits.h>   /* PATH_MAX, INT_MAX (via vdso/limits.h) */
#include <linux/security.h> /* security_secctx_to_secid() */
#include <linux/proc_fs.h>  /* proc_create() for /proc/susfs_hide_mounts */
#include <linux/version.h>  /* LINUX_VERSION_CODE / KERNEL_VERSION: nothing else here
                             * pulled version.h in, and -Werror=undef turned the
                             * version gates below into hard errors when it was missing */
#include <linux/rbtree.h>   /* >= 6.12: ns->mounts is an rb-tree, not a list */
#include <linux/rwsem.h>    /* >= 6.12: namespace_sem is a struct rw_semaphore */
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
#include <linux/workqueue.h> /* >= 6.12: the deferred walk of a cloned namespace */
#endif
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 18, 0)
#include <linux/xarray.h>   /* >= 6.18: struct xarray + XA_LIMIT()/xa_lock() for mnt_id_xa */
#endif
#include "mount.h"      /* fs/mount.h: struct mount + struct mnt_namespace + real_mount() */
#include "symbol_resolver.h"
#include "susfs_abi.h"
#include "susfs_log.h"
#include "susfs.h"	/* module-wide declarations */

#define SUS_MOUNT_KEEP_MAX 8
#define SUS_MOUNT_KEEP_LEN 128
#define SUS_MOUNT_KEEP_CMDLINE (SUS_MOUNT_KEEP_MAX * (SUS_MOUNT_KEEP_LEN + 2) + 32)

static char mount_keep[SUS_MOUNT_KEEP_MAX][SUS_MOUNT_KEEP_LEN];
static int n_mount_keep;
static DEFINE_SPINLOCK(mount_keep_lock);
static const char *const mount_keep_default = "/data/adb/";
static atomic_t n_keep_rescans = ATOMIC_INIT(0);

static int n_show_probes;

#define DEFAULT_KSU_MNT_ID 2000000000ULL

#define SUS_MOUNT_MIN_SANE_MNT_ID 1000

#define SUS_MOUNT_MAX_SCAN 65536

#define SUS_MOUNT_KSU_ID_MIN ((unsigned int)DEFAULT_KSU_MNT_ID)

static unsigned long param_min_mnt_id = DEFAULT_KSU_MNT_ID;
module_param_named(min_mnt_id, param_min_mnt_id, ulong, 0644);

static char param_su_ctx[128] = "u:r:ksu:s0";
module_param_string(su_ctx, param_su_ctx, sizeof(param_su_ctx), 0644);

static u32 su_sid;

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 18, 0)
static struct xarray *sus_mount_mnt_id_xa;
static int (*pfn_xa_alloc)(struct xarray *xa, u32 *id, void *entry,
                           struct xa_limit limit, gfp_t gfp);
static void *(*pfn_xa_erase)(struct xarray *xa, unsigned long index);

static const char *sus_mount_xa_obj_src = "none";
static const char *sus_mount_xa_alloc_src = "none";
static const char *sus_mount_xa_erase_src = "none";

extern struct xarray mnt_id_xa;
extern int __xa_alloc(struct xarray *xa, u32 *id, void *entry,
                      struct xa_limit limit, gfp_t gfp);
extern void *__xa_erase(struct xarray *xa, unsigned long index);
#else
static struct ida *sus_mount_mnt_id_ida;
static int (*pfn_ida_alloc_range)(struct ida *ida, unsigned int min,
                                  unsigned int max, gfp_t gfp);
static void (*pfn_ida_free)(struct ida *ida, unsigned int id);
#endif

static bool sus_mount_ida_ready(void)
{
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 18, 0)
    return sus_mount_mnt_id_xa && pfn_xa_alloc && pfn_xa_erase;
#else
    return sus_mount_mnt_id_ida && pfn_ida_alloc_range && pfn_ida_free;
#endif
}

static void (*pfn_security_cred_getsecid)(const struct cred *cred, u32 *secid);
static char *(*pfn_d_path)(const struct path *path, char *buf, int buflen);

static __nocfi bool sus_mount_is_su_domain(void)
{
    u32 sid = 0;

    if (!pfn_security_cred_getsecid || !su_sid)
        return false;

    pfn_security_cred_getsecid(current_cred(), &sid);
    return sid == su_sid;
}

static __nocfi int sus_mount_ida_alloc(void)
{
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 18, 0)
    struct xa_limit limit = XA_LIMIT((u32)DEFAULT_KSU_MNT_ID, (u32)(INT_MAX - 1));
    u32 id = 0;
    int ret;

    xa_lock(sus_mount_mnt_id_xa);
    ret = pfn_xa_alloc(sus_mount_mnt_id_xa, &id, NULL, limit, GFP_KERNEL);
    xa_unlock(sus_mount_mnt_id_xa);
    if (ret)
        return ret;
    return (int)id;
#else
    return pfn_ida_alloc_range(sus_mount_mnt_id_ida,
                               (unsigned int)DEFAULT_KSU_MNT_ID,
                               (unsigned int)(INT_MAX - 1), GFP_KERNEL);
#endif
}

static __nocfi void sus_mount_ida_release(int id)
{
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 18, 0)
    xa_lock(sus_mount_mnt_id_xa);
    pfn_xa_erase(sus_mount_mnt_id_xa, (unsigned long)(unsigned int)id);
    xa_unlock(sus_mount_mnt_id_xa);
#else
    pfn_ida_free(sus_mount_mnt_id_ida, (unsigned int)id);
#endif
}

static __nocfi char *sus_mount_d_path(const struct path *path, char *buf, int buflen)
{
    if (!pfn_d_path)
        return ERR_PTR(-ENOSYS);
    return pfn_d_path(path, buf, buflen);
}

static unsigned long sus_mount_min_mnt_id(void)
{
    if (param_min_mnt_id < SUS_MOUNT_MIN_SANE_MNT_ID)
        return DEFAULT_KSU_MNT_ID;
    return param_min_mnt_id;
}

static bool mount_registered;

/* Serialises the enable/disable control surface.  The supercall handler runs from the caller's
 * task_work, i.e. in process context, so two tasks can enter sus_mount_register()/
 * sus_mount_unregister() at the same time.  Both do check-then-act on `mount_registered` and
 * then call register_kprobe()/register_kretprobe(), which sleep - and registering the same probe
 * object twice is not harmless: an address-registered kretprobe goes through warn_kprobe_rereg()
 * (a WARN_ON_ONCE with a stack trace naming this module), while a name-registered one fails and
 * the caller reports -EINVAL to userspace even though the other task armed it.  sus_path.c
 * (sus_path_arm_lock) and susfs_kstat.c (kstat_lock) already serialise their arm paths this way. */
static DEFINE_MUTEX(sus_mount_ctl_lock);

#define SUS_MOUNT_IDMAP_MAX 64

/* sus_id == 0 marks a free slot; mnt ids are never 0. */
struct sus_mount_idmap_entry {
    int sus_id;
    int shown_id;
    dev_t s_dev;	/* the superblock the mount lived on (see the drop note) */
};

static struct sus_mount_idmap_entry mount_idmap[SUS_MOUNT_IDMAP_MAX];
static int n_idmap;
static DEFINE_SPINLOCK(idmap_lock);
static atomic_t n_idmap_recycled = ATOMIC_INIT(0);	/* stale entries dropped */
static atomic_t n_idmap_dropped_dev = ATOMIC_INIT(0);	/* dropped at sb teardown */

static atomic_t n_fdinfo_hits = ATOMIC_INIT(0);
static atomic_t n_fdinfo_rewrites = ATOMIC_INIT(0);
static atomic_t n_statx_hits = ATOMIC_INIT(0);
static atomic_t n_statx_rewrites = ATOMIC_INIT(0);

static void sus_mount_idmap_add(int sus_id, int shown_id, dev_t s_dev)
{
    unsigned long flags;
    int i, slot = -1;

    if (sus_id <= 0 || shown_id <= 0)
        return;
    spin_lock_irqsave(&idmap_lock, flags);

    for (i = 0; i < n_idmap; i++) {
        if (mount_idmap[i].sus_id == sus_id) {
            mount_idmap[i].shown_id = shown_id;
            mount_idmap[i].s_dev = s_dev;
            goto out;
        }
        if (!mount_idmap[i].sus_id && slot < 0)
            slot = i;
    }
    if (slot < 0) {
        if (n_idmap >= SUS_MOUNT_IDMAP_MAX)
            goto out;
        slot = n_idmap++;
    }
    mount_idmap[slot].sus_id = sus_id;
    mount_idmap[slot].shown_id = shown_id;
    mount_idmap[slot].s_dev = s_dev;
out:
    spin_unlock_irqrestore(&idmap_lock, flags);
}

static void sus_mount_idmap_drop_dev(dev_t s_dev)
{
    unsigned long flags;
    int i;

    spin_lock_irqsave(&idmap_lock, flags);
    for (i = 0; i < n_idmap; i++) {
        if (mount_idmap[i].sus_id && mount_idmap[i].s_dev == s_dev) {
            mount_idmap[i].sus_id = 0;
            mount_idmap[i].shown_id = 0;
            atomic_inc(&n_idmap_dropped_dev);
        }
    }
    spin_unlock_irqrestore(&idmap_lock, flags);
}

static void sus_mount_idmap_drop(int sus_id)
{
    unsigned long flags;
    int i;

    if (sus_id <= 0)
        return;
    spin_lock_irqsave(&idmap_lock, flags);
    for (i = 0; i < n_idmap; i++) {
        if (mount_idmap[i].sus_id == sus_id) {
            mount_idmap[i].sus_id = 0;
            mount_idmap[i].shown_id = 0;
            atomic_inc(&n_idmap_recycled);
            break;
        }
    }
    spin_unlock_irqrestore(&idmap_lock, flags);
}

/* 0 means "not one of ours" - mnt_id 0 is never handed out. */
static int sus_mount_shown_for(int sus_id)
{
    unsigned long flags;
    int i, shown = 0;

    if (sus_id <= 0)
        return 0;
    spin_lock_irqsave(&idmap_lock, flags);
    for (i = 0; i < n_idmap; i++) {
        if (mount_idmap[i].sus_id == sus_id) {
            shown = mount_idmap[i].shown_id;
            break;
        }
    }
    spin_unlock_irqrestore(&idmap_lock, flags);
    return shown;
}

static int sus_mount_shown_id(struct mount *mnt)
{
    while (mnt && mnt->mnt_parent && mnt != mnt->mnt_parent &&
           (unsigned int)mnt->mnt_id >= SUS_MOUNT_KSU_ID_MIN)
        mnt = mnt->mnt_parent;
    return mnt ? mnt->mnt_id : 0;
}

#define SUS_MOUNT_DEVNAME_MAX 64
#define SUS_MOUNT_IDENT_MAX 32
/* Defined with the scan helpers further down; the identity test needs it here. */
static bool sus_mount_path_is_ours(const char *s);

struct sus_mount_ident {
    dev_t s_dev;
    unsigned long root_ino;	/* 0 = free slot */
    bool devname_is_path;

    bool devname_truncated;
    char devname[SUS_MOUNT_DEVNAME_MAX];
};

static struct sus_mount_ident mount_ident[SUS_MOUNT_IDENT_MAX];
static int n_ident;
static DEFINE_SPINLOCK(ident_lock);
static atomic_t n_ident_hits = ATOMIC_INIT(0);		/* hidden by identity, not by id */
static atomic_t n_ident_learned = ATOMIC_INIT(0);	/* ids learned while hiding */
static atomic_t n_ident_full = ATOMIC_INIT(0);		/* records that found no slot */
static atomic_t n_ident_dropped_dev = ATOMIC_INIT(0);	/* records dropped at sb teardown */
static atomic_t n_sb_down = ATOMIC_INIT(0);		/* superblocks seen shut down */

static int mount_dbg;
module_param_named(mount_dbg, mount_dbg, int, 0644);

static atomic_t n_dbg_logged = ATOMIC_INIT(0);

static void sus_mount_ident_add(struct mount *r)
{
    const char *devname = r->mnt_devname;
    struct dentry *root = r->mnt.mnt_root;
    unsigned long ino;
    unsigned long flags;
    int i, slot = -1;

    if (!root || !root->d_inode)
        return;
    ino = root->d_inode->i_ino;
    if (!ino)
        return;

    spin_lock_irqsave(&ident_lock, flags);
    /* Re-check under the lock so two scans cannot both append; a re-enable finds them here. */
    for (i = 0; i < n_ident; i++) {
        if (mount_ident[i].s_dev == r->mnt.mnt_sb->s_dev &&
            mount_ident[i].root_ino == ino)
            goto out;
        if (!mount_ident[i].root_ino && slot < 0)
            slot = i;
    }
    if (slot < 0) {
        if (n_ident >= SUS_MOUNT_IDENT_MAX) {
            /* Silent truncation is a "registered but not effective" failure; say it once. */
            if (atomic_inc_return(&n_ident_full) == 1)
                pr_warn("sus_mount: identity table full (%d), %s is NOT recognised in other namespaces\n",
                        SUS_MOUNT_IDENT_MAX,
                        devname ? devname : "(no devname)");
            goto out;
        }
        slot = n_ident;
        smp_store_release(&n_ident, n_ident + 1);
    }
    {
        struct sus_mount_ident *e = &mount_ident[slot];

        e->s_dev = r->mnt.mnt_sb->s_dev;
        e->devname_is_path = devname && devname[0] == '/';
        if (e->devname_is_path) {
            e->devname_truncated = strlen(devname) >= sizeof(e->devname);
            strscpy(e->devname, devname, sizeof(e->devname));
        } else {
            e->devname[0] = '\0';
        }
        if (mount_dbg)
            SUSFS_LOGI("sus_mount: ident[%d] s_dev=%u root_ino=%lu devname=%s\n",
                    slot, (unsigned int)e->s_dev, ino,
                    e->devname_is_path ? e->devname : "(not path-shaped)");
        /* Set LAST: root_ino != 0 is what makes the record live for the readers. */
        smp_store_release(&e->root_ino, ino);
    }
out:
    spin_unlock_irqrestore(&ident_lock, flags);
}

/* Interrupt-context safe (kprobe pre_handler): read-only, no sleeping. */
static bool sus_mount_ident_match(struct mount *r)
{
    int n = smp_load_acquire(&n_ident);
    const char *devname = r->mnt_devname;
    struct dentry *root = r->mnt.mnt_root;
    unsigned long ino = (root && root->d_inode) ? root->d_inode->i_ino : 0;
    int i;

    for (i = 0; i < n; i++) {
        const struct sus_mount_ident *e = &mount_ident[i];
        unsigned long e_ino = smp_load_acquire(&e->root_ino);

        if (e_ino && e_ino == ino && e->s_dev == r->mnt.mnt_sb->s_dev)
            return true;
        if (e->devname_is_path && devname &&
            (e->devname_truncated
                 ? !strncmp(e->devname, devname, sizeof(e->devname) - 1)
                 : !strcmp(e->devname, devname)))
            return true;
    }
    return false;
}

static void sus_mount_ident_drop_dev(dev_t s_dev)
{
    unsigned long flags;
    int i;

    spin_lock_irqsave(&ident_lock, flags);
    for (i = 0; i < n_ident; i++) {
        if (smp_load_acquire(&mount_ident[i].root_ino) && mount_ident[i].s_dev == s_dev) {
            smp_store_release(&mount_ident[i].root_ino, 0);
            atomic_inc(&n_ident_dropped_dev);
        }
    }
    spin_unlock_irqrestore(&ident_lock, flags);
}

static int sus_mount_sb_down_pre(struct kprobe *kp, struct pt_regs *regs)
{
    struct super_block *sb = (struct super_block *)regs->regs[0];

    atomic_inc(&n_sb_down);
    if (!sb)
        return 0;
    sus_mount_ident_drop_dev(sb->s_dev);
    sus_mount_idmap_drop_dev(sb->s_dev);
    return 0;
}

static struct kprobe kp_sb_down = {
    .symbol_name = "generic_shutdown_super",
    .pre_handler = sus_mount_sb_down_pre,
};
static bool kp_sb_down_ok;

static bool sus_mount_is_ours(struct mount *r)
{
    if ((unsigned int)r->mnt_id >= SUS_MOUNT_KSU_ID_MIN)
        return true;
    if (sus_mount_path_is_ours(r->mnt_devname))
        return true;
    return sus_mount_ident_match(r);
}

static int sus_mount_shown_id_from(struct mount *mnt)
{
    if (mnt && (unsigned int)mnt->mnt_id < SUS_MOUNT_KSU_ID_MIN)
        mnt = mnt->mnt_parent;
    while (mnt && mnt->mnt_parent && mnt != mnt->mnt_parent &&
           sus_mount_is_ours(mnt))
        mnt = mnt->mnt_parent;
    return mnt ? (int)mnt->mnt_id : 0;
}

static void sus_mount_note_id(struct mount *r)
{
    int shown;

    if (sus_mount_shown_for((int)r->mnt_id))
        return;
    shown = sus_mount_shown_id_from(r);
    if (shown > 0 && shown != (int)r->mnt_id) {
        sus_mount_idmap_add((int)r->mnt_id, shown, r->mnt.mnt_sb->s_dev);
        atomic_inc(&n_ident_learned);
    }
}

static atomic_t n_clone_walks = ATOMIC_INIT(0);
static atomic_t n_clone_learned = ATOMIC_INIT(0);
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
static atomic_t n_clone_queued = ATOMIC_INIT(0);
static atomic_t n_clone_dropped = ATOMIC_INIT(0);
static atomic_t n_clone_refused_logged = ATOMIC_INIT(0);
#endif

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
static struct rw_semaphore *sus_mount_namespace_sem;

static bool sus_mount_ns_walk_begin(void)
{
    if (!sus_mount_namespace_sem)
        return false;
    down_read(sus_mount_namespace_sem);
    return true;
}

static void sus_mount_ns_walk_end(void)
{
    up_read(sus_mount_namespace_sem);
}

#define SUS_MOUNT_ITER_TYPE		struct rb_node *
#define SUS_MOUNT_ITER_FOR(ns, it)	for ((it) = rb_first(&(ns)->mounts); (it); (it) = rb_next(it))
#define SUS_MOUNT_ITER_MOUNT(it)	rb_entry((it), struct mount, mnt_node)
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 13, 0)
#define SUS_MOUNT_MNT_NOT_IN_NS(r, ns)	((r)->mnt_ns != (ns) || !mnt_ns_attached(r))
#else

#define SUS_MOUNT_MNT_NOT_IN_NS(r, ns)	((r)->mnt_ns != (ns) || RB_EMPTY_NODE(&(r)->mnt_node))
#endif
#else
static bool sus_mount_ns_walk_begin(void)
{
    return true;	/* the caller takes ns_lock instead */
}

static void sus_mount_ns_walk_end(void)
{
}

#define SUS_MOUNT_ITER_TYPE		struct list_head *
#define SUS_MOUNT_ITER_FOR(ns, it)	for ((it) = (ns)->list.next; (it) != &(ns)->list; (it) = (it)->next)
#define SUS_MOUNT_ITER_MOUNT(it)	list_entry((it), struct mount, mnt_list)
#define SUS_MOUNT_MNT_NOT_IN_NS(r, ns)	((r)->mnt_ns != (ns) || ((r)->mnt.mnt_flags & MNT_CURSOR))
#endif

#if LINUX_VERSION_CODE < KERNEL_VERSION(6, 12, 0)

static void sus_mount_learn_ns(struct mnt_namespace *ns)
{
    SUS_MOUNT_ITER_TYPE pos;
    struct mount *r;
    int learned = 0;

    spin_lock(&ns->ns_lock);
    SUS_MOUNT_ITER_FOR(ns, pos) {
        int shown;

        r = SUS_MOUNT_ITER_MOUNT(pos);
        if (SUS_MOUNT_MNT_NOT_IN_NS(r, ns))
            continue;
        if (!sus_mount_is_ours(r))
            continue;
        if (sus_mount_shown_for((int)r->mnt_id))
            continue;
        shown = sus_mount_shown_id_from(r);
        if (shown > 0 && shown != (int)r->mnt_id) {
            sus_mount_idmap_add((int)r->mnt_id, shown, r->mnt.mnt_sb->s_dev);
            learned++;
        }
    }
    spin_unlock(&ns->ns_lock);
    atomic_inc(&n_clone_walks);
    if (learned)
        atomic_add(learned, &n_clone_learned);
}
#else

#define SUS_MOUNT_LEARN_RING 16
static struct mnt_namespace *sus_mount_learn_ring[SUS_MOUNT_LEARN_RING];
static unsigned int sus_mount_learn_head, sus_mount_learn_tail;
static DEFINE_SPINLOCK(sus_mount_learn_lock);
static void (*pfn_put_mnt_ns)(struct mnt_namespace *ns);
static void sus_mount_learn_work(struct work_struct *w);
static DECLARE_WORK(sus_mount_learn_wq, sus_mount_learn_work);

static __nocfi void sus_mount_put_mnt_ns(struct mnt_namespace *ns)
{
    pfn_put_mnt_ns(ns);
}

/* One recorded namespace, or NULL when the ring is empty. */
static struct mnt_namespace *sus_mount_learn_pop(void)
{
    unsigned long flags;
    struct mnt_namespace *ns;

    spin_lock_irqsave(&sus_mount_learn_lock, flags);
    if (sus_mount_learn_head == sus_mount_learn_tail) {
        spin_unlock_irqrestore(&sus_mount_learn_lock, flags);
        return NULL;
    }
    ns = sus_mount_learn_ring[sus_mount_learn_tail];
    sus_mount_learn_ring[sus_mount_learn_tail] = NULL;
    sus_mount_learn_tail = (sus_mount_learn_tail + 1) % SUS_MOUNT_LEARN_RING;
    spin_unlock_irqrestore(&sus_mount_learn_lock, flags);
    return ns;
}

static int sus_mount_learn_ns_walk(struct mnt_namespace *ns)
{
    SUS_MOUNT_ITER_TYPE pos;
    unsigned int seen = 0;
    int learned = 0;

    if (!sus_mount_ns_walk_begin())
        return -ENOSYS;

    rcu_read_lock();
    SUS_MOUNT_ITER_FOR(ns, pos) {
        struct mount *r;
        int shown;

        if (seen++ >= SUS_MOUNT_MAX_SCAN)
            break;
        r = SUS_MOUNT_ITER_MOUNT(pos);
        if (SUS_MOUNT_MNT_NOT_IN_NS(r, ns))
            continue;
        if (!sus_mount_is_ours(r))
            continue;
        if (sus_mount_shown_for((int)r->mnt_id))
            continue;
        shown = sus_mount_shown_id_from(r);
        if (shown > 0 && shown != (int)r->mnt_id) {
            sus_mount_idmap_add((int)r->mnt_id, shown, r->mnt.mnt_sb->s_dev);
            learned++;
        }
    }
    rcu_read_unlock();
    sus_mount_ns_walk_end();
    return learned;
}

static void sus_mount_learn_work(struct work_struct *w)
{
    struct mnt_namespace *ns;

    while ((ns = sus_mount_learn_pop()) != NULL) {
        int learned = sus_mount_learn_ns_walk(ns);

        if (learned == -ENOSYS && !atomic_xchg(&n_clone_refused_logged, 1))
            pr_warn("sus_mount: namespace_sem could not be resolved at load time - refusing to walk a cloned namespace without the lock the kernel's own mount-table iterator holds (that namespace's ids stay unlearned)\n");
        atomic_inc(&n_clone_walks);
        if (learned > 0)
            atomic_add(learned, &n_clone_learned);
        /* After sus_mount_ns_walk_end(): see the note above about 6.18. */
        sus_mount_put_mnt_ns(ns);
    }
}

/* Called from the copy_mnt_ns return probe: no allocation, no sleeping. */
static void sus_mount_defer_learn_ns(struct mnt_namespace *ns)
{
    unsigned int next;
    unsigned long flags;

    if (!pfn_put_mnt_ns) {
        atomic_inc(&n_clone_dropped);
        return;
    }
    get_mnt_ns(ns);

    spin_lock_irqsave(&sus_mount_learn_lock, flags);
    next = (sus_mount_learn_head + 1) % SUS_MOUNT_LEARN_RING;
    if (next == sus_mount_learn_tail) {
        spin_unlock_irqrestore(&sus_mount_learn_lock, flags);
        sus_mount_put_mnt_ns(ns);
        atomic_inc(&n_clone_dropped);
        return;
    }
    sus_mount_learn_ring[sus_mount_learn_head] = ns;
    sus_mount_learn_head = next;
    spin_unlock_irqrestore(&sus_mount_learn_lock, flags);

    atomic_inc(&n_clone_queued);
    schedule_work(&sus_mount_learn_wq);
}

static void sus_mount_learn_stop(void)
{
    struct mnt_namespace *ns;

    cancel_work_sync(&sus_mount_learn_wq);
    while ((ns = sus_mount_learn_pop()) != NULL)
        sus_mount_put_mnt_ns(ns);
}
#endif

struct sus_mount_clone_state {
    unsigned long flags;
};

static int sus_mount_clone_entry(struct kretprobe_instance *ri, struct pt_regs *regs)
{
    struct sus_mount_clone_state *st = (struct sus_mount_clone_state *)ri->data;

    st->flags = regs->regs[0];
    return 0;
}

static int sus_mount_clone_ret(struct kretprobe_instance *ri, struct pt_regs *regs)
{
    struct sus_mount_clone_state *st = (struct sus_mount_clone_state *)ri->data;
    struct mnt_namespace *ns = (struct mnt_namespace *)regs_return_value(regs);

    if (!(st->flags & CLONE_NEWNS))
        return 0;			/* plain fork: the current namespace, not a copy */
    if (IS_ERR_OR_NULL(ns))
        return 0;
#if LINUX_VERSION_CODE < KERNEL_VERSION(6, 12, 0)
    sus_mount_learn_ns(ns);
#else
    sus_mount_defer_learn_ns(ns);
#endif
    return 0;
}

static struct kretprobe kr_clone_ns = {
    .kp.symbol_name = "copy_mnt_ns",
    .entry_handler = sus_mount_clone_entry,
    .handler = sus_mount_clone_ret,
    .data_size = sizeof(struct sus_mount_clone_state),
    .maxactive = 16,
};
static bool kr_clone_ns_ok;

#define SUS_MOUNT_NEWMNT_PATH_MAX 256

static atomic_t n_newmnt_seen = ATOMIC_INIT(0);
static atomic_t n_newmnt_recorded = ATOMIC_INIT(0);
static atomic_t n_newmnt_pathfail = ATOMIC_INIT(0);

struct sus_mount_newmnt_state {
    struct mount *m;
};

static int sus_mount_newmnt_entry(struct kretprobe_instance *ri, struct pt_regs *regs)
{
    struct sus_mount_newmnt_state *st = (struct sus_mount_newmnt_state *)ri->data;

    st->m = (struct mount *)regs->regs[0];	/* source_mnt */
    return 0;
}

static bool sus_mount_should_record(struct mount *r, char *buf, int buflen, char **why)
{
    struct path p;
    char *dp;

    if (sus_mount_path_is_ours(r->mnt_devname)) {
        *why = "devname";
        return true;
    }
    if (!pfn_d_path)
        return false;
    p.mnt = &r->mnt;
    p.dentry = r->mnt.mnt_root;
    dp = sus_mount_d_path(&p, buf, buflen);
    if (IS_ERR_OR_NULL(dp)) {
        atomic_inc(&n_newmnt_pathfail);
        return false;
    }
    if (sus_mount_path_is_ours(dp)) {
        *why = dp;
        return true;
    }
    return false;
}

static int sus_mount_newmnt_ret(struct kretprobe_instance *ri, struct pt_regs *regs)
{
    struct sus_mount_newmnt_state *st = (struct sus_mount_newmnt_state *)ri->data;
    struct mount *r = st->m;
    char buf[SUS_MOUNT_NEWMNT_PATH_MAX];
    char *why = NULL;

    if (!susfs_ptr_plausible(r) || (long)regs_return_value(regs) != 0)
        return 0;			/* the attach failed: nothing was mounted */
    atomic_inc(&n_newmnt_seen);

    if (!r->mnt_parent || r->mnt_parent == r)
        return 0;
    if (!sus_mount_should_record(r, buf, sizeof(buf), &why))
        return 0;

    sus_mount_ident_add(r);
    sus_mount_note_id(r);
    atomic_inc(&n_newmnt_recorded);
    SUSFS_LOGI("sus_mount: learned mount at %s (mnt_id %d, devname %s)\n",
            why, r->mnt_id, r->mnt_devname ? r->mnt_devname : "none");
    return 0;
}

static struct kretprobe kr_newmnt = {
    .kp.symbol_name = "attach_recursive_mnt",
    .entry_handler = sus_mount_newmnt_entry,
    .handler = sus_mount_newmnt_ret,
    .data_size = sizeof(struct sus_mount_newmnt_state),
    .maxactive = 16,
};
static bool kr_newmnt_ok;

#define SUS_MOUNT_MNTID_LABEL		"mnt_id:\t"
#define SUS_MOUNT_MNTID_LABEL_LEN	8

struct sus_mount_kretprobe_state {
    struct seq_file *m;		/* fdinfo: the seq_file being filled */
    unsigned long ubuf;		/* statx: the caller's struct statx __user * */
    char where;			/* statx: 's' = __arm64_sys_statx, 'd' = do_statx */
};

static atomic_t n_fdinfo_entry = ATOMIC_INIT(0);
static atomic_t n_fdinfo_nolabel = ATOMIC_INIT(0);

static int sus_mount_fdinfo_entry(struct kretprobe_instance *ri, struct pt_regs *regs)
{
    struct sus_mount_kretprobe_state *st = (struct sus_mount_kretprobe_state *)ri->data;

    atomic_inc(&n_fdinfo_entry);

    st->m = susfs_ptr_plausible((void *)regs->regs[0])
               ? (struct seq_file *)regs->regs[0] : NULL;
    return 0;
}

static bool sus_mount_fdinfo_replace_mntid(struct seq_file *m)
{
    char *buf = m->buf, digits[12];
    size_t count = m->count, i, pos = 0, len = 0, n = 0;
    unsigned long old = 0;
    int shown;
    unsigned int v;

    for (i = 0; i + SUS_MOUNT_MNTID_LABEL_LEN < count; i++) {
        if (!memcmp(buf + i, SUS_MOUNT_MNTID_LABEL, SUS_MOUNT_MNTID_LABEL_LEN)) {
            pos = i + SUS_MOUNT_MNTID_LABEL_LEN;
            break;
        }
    }
    if (!pos)
        return false;

    while (pos + len < count && len < 10 &&
           buf[pos + len] >= '0' && buf[pos + len] <= '9') {
        old = old * 10 + (unsigned long)(buf[pos + len] - '0');
        len++;
    }
    if (!len)
        return false;

    shown = sus_mount_shown_for((int)old);
    if (shown <= 0)
        return false;

    v = (unsigned int)shown;
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
        memmove(buf + pos + n, buf + pos + len, count - (pos + len));
    memcpy(buf + pos, digits, n);
    m->count = count - len + n;
    return true;
}

static int sus_mount_fdinfo_ret(struct kretprobe_instance *ri, struct pt_regs *regs)
{
    struct sus_mount_kretprobe_state *st = (struct sus_mount_kretprobe_state *)ri->data;
    struct seq_file *m = st->m;

    if (!m || (long)regs_return_value(regs) != 0)
        return 0;
    if (!m->buf || !m->count)
        return 0;

    if (!m->file || !m->file->f_path.dentry || !m->file->f_path.dentry->d_parent ||
        strcmp(m->file->f_path.dentry->d_parent->d_name.name, "fdinfo") != 0) {
        atomic_inc(&n_fdinfo_nolabel);
        return 0;
    }

    if (sus_mount_is_su_domain())
        return 0;

    atomic_inc(&n_fdinfo_hits);

    if (sus_mount_fdinfo_replace_mntid(m))
        atomic_inc(&n_fdinfo_rewrites);
    else
        atomic_inc(&n_fdinfo_nolabel);
    return 0;
}

#define SUS_MOUNT_FDINFO_MAX 8

static struct kretprobe kr_fdinfo[SUS_MOUNT_FDINFO_MAX];
static int n_fdinfo_probes;
static bool kr_fdinfo_ok;

static int sus_mount_fdinfo_arm(void)
{
    unsigned long addrs[SUS_MOUNT_FDINFO_MAX];
    int i, n;

    n = ksu_find_symbol_all("seq_show", addrs, SUS_MOUNT_FDINFO_MAX);
    if (n <= 0) {
        pr_warn("sus_mount: seq_show not resolved - fdinfo keeps printing the real mnt_id\n");
        return -ENOENT;
    }
    for (i = 0; i < n; i++) {
        struct kretprobe *kr = &kr_fdinfo[i];
        int rc;

        kr->kp.addr = (void *)addrs[i];
        kr->entry_handler = sus_mount_fdinfo_entry;
        kr->handler = sus_mount_fdinfo_ret;
        kr->data_size = sizeof(struct sus_mount_kretprobe_state);
        kr->maxactive = 16;
        rc = register_kretprobe(kr);
        if (rc) {
            pr_warn("sus_mount: register_kretprobe(seq_show @%px) failed %d\n", (void *)addrs[i], rc);
            kr->kp.addr = NULL;
            continue;
        }
        n_fdinfo_probes++;
    }
    if (!n_fdinfo_probes)
        return -EINVAL;
    SUSFS_LOGI("sus_mount: fdinfo hooked on %d/%d seq_show symbol(s)\n", n_fdinfo_probes, n);
    kr_fdinfo_ok = true;
    return 0;
}

static void sus_mount_fdinfo_disarm(void)
{
    int i;

    for (i = 0; i < SUS_MOUNT_FDINFO_MAX; i++) {
        if (!kr_fdinfo[i].kp.addr)
            continue;
        unregister_kretprobe(&kr_fdinfo[i]);
        kr_fdinfo[i].kp.addr = NULL;
    }
    n_fdinfo_probes = 0;
    kr_fdinfo_ok = false;
}

static atomic_t n_statx_entry = ATOMIC_INIT(0);
static atomic_t n_statx_ret = ATOMIC_INIT(0);
static atomic_t n_statx_nobuf = ATOMIC_INIT(0);
static atomic_t n_statx_err = ATOMIC_INIT(0);
static atomic_t n_statx_copyfail = ATOMIC_INIT(0);
static atomic_t n_statx_nomap = ATOMIC_INIT(0);

static int sus_mount_statx_entry_sys(struct kretprobe_instance *ri, struct pt_regs *regs)
{
    struct sus_mount_kretprobe_state *st = (struct sus_mount_kretprobe_state *)ri->data;
    const struct pt_regs *uregs = (const struct pt_regs *)regs->regs[0];

    atomic_inc(&n_statx_entry);
    st->where = 's';
    st->ubuf = uregs ? (unsigned long)uregs->regs[4] : 0;
    return 0;
}

static int sus_mount_statx_entry_do(struct kretprobe_instance *ri, struct pt_regs *regs)
{
    struct sus_mount_kretprobe_state *st = (struct sus_mount_kretprobe_state *)ri->data;

    atomic_inc(&n_statx_entry);
    st->where = 'd';
    st->ubuf = regs->regs[4];
    return 0;
}

static int sus_mount_statx_ret(struct kretprobe_instance *ri, struct pt_regs *regs)
{
    struct sus_mount_kretprobe_state *st = (struct sus_mount_kretprobe_state *)ri->data;
    unsigned long ubuf = st->ubuf;
    u64 id = 0, shown;
    int new_id;

    atomic_inc(&n_statx_ret);
    if ((long)regs_return_value(regs) != 0) {
        atomic_inc(&n_statx_err);
        return 0;
    }
    if (!ubuf) {

        atomic_inc(&n_statx_nobuf);
        pr_info_ratelimited("sus_mount: statx landing point %c had no buffer\n",
                            st->where);
        return 0;
    }
    if (sus_mount_is_su_domain())
        return 0;

    atomic_inc(&n_statx_hits);
    if (copy_from_user(&id, (void __user *)(ubuf + offsetof(struct statx, stx_mnt_id)),
                       sizeof(id))) {
        atomic_inc(&n_statx_copyfail);
        return 0;
    }
    new_id = sus_mount_shown_for((int)id);
    if (new_id <= 0) {
        atomic_inc(&n_statx_nomap);
        return 0;
    }
    shown = (u64)new_id;
    if (copy_to_user((void __user *)(ubuf + offsetof(struct statx, stx_mnt_id)),
                     &shown, sizeof(shown))) {
        atomic_inc(&n_statx_copyfail);
        return 0;
    }
    atomic_inc(&n_statx_rewrites);
    return 0;
}

static struct kretprobe kr_statx = {
    .kp.symbol_name = "__arm64_sys_statx",
    .entry_handler = sus_mount_statx_entry_sys,
    .handler = sus_mount_statx_ret,
    .data_size = sizeof(struct sus_mount_kretprobe_state),
    .maxactive = 16,
};
static bool kr_statx_ok;

static struct kretprobe kr_statx_do = {
    .kp.symbol_name = "do_statx",
    .entry_handler = sus_mount_statx_entry_do,
    .handler = sus_mount_statx_ret,
    .data_size = sizeof(struct sus_mount_kretprobe_state),
    .maxactive = 16,
};
static bool kr_statx_do_ok;

static int sus_mount_idmap_live(void)
{
    unsigned long flags;
    int i, live = 0;

    spin_lock_irqsave(&idmap_lock, flags);
    for (i = 0; i < n_idmap; i++)
        if (mount_idmap[i].sus_id)
            live++;
    spin_unlock_irqrestore(&idmap_lock, flags);
    return live;
}

static int sus_mount_ident_live(void)
{
    unsigned long flags;
    int i, live = 0;

    spin_lock_irqsave(&ident_lock, flags);
    for (i = 0; i < READ_ONCE(n_ident); i++)
        if (smp_load_acquire(&mount_ident[i].root_ino))
            live++;
    spin_unlock_irqrestore(&ident_lock, flags);
    return live;
}

static int sus_mount_stat_show(char *buf, const struct kernel_param *kp)
{
    return scnprintf(buf, PAGE_SIZE,
                     "idmap=%d/%d  ident=%d/%d  hide=%d su_domain=%d\n"
                     "show_probes=%d/3 (show_vfsstat/show_mountinfo/show_vfsmnt)\n"
                     "ident: hits=%d learned_ids=%d full=%d dropped_dev=%d\n"
                     "idmap: recycled_dropped=%d dropped_dev=%d\n"
                     "sb: down=%d (probe=%d)\n"
                     "clone: walks=%d learned=%d (probe=%d)\n"
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
                     "clone_defer: queued=%d dropped=%d\n"
#endif
                     "newmount: seen=%d recorded=%d pathfail=%d (probe=%d)\n"
                     "keep: prefixes=%d rescans=%d\n"
                     "fdinfo: probes=%d entry=%d hits=%d rewrites=%d nolabel=%d\n"
                     "statx: entry=%d ret=%d hits=%d rewrites=%d nobuf=%d err=%d copyfail=%d nomap=%d "
                     "(sys=%d do=%d)\n",
                     sus_mount_idmap_live(), n_idmap,
                     sus_mount_ident_live(), READ_ONCE(n_ident), mount_registered,
                     (int)sus_mount_is_su_domain(),
                     n_show_probes,
                     atomic_read(&n_ident_hits), atomic_read(&n_ident_learned),
                     atomic_read(&n_ident_full),
                     atomic_read(&n_ident_dropped_dev),
                     atomic_read(&n_idmap_recycled),
                     atomic_read(&n_idmap_dropped_dev),
                     atomic_read(&n_sb_down), (int)kp_sb_down_ok,
                     atomic_read(&n_clone_walks), atomic_read(&n_clone_learned),
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
                     atomic_read(&n_clone_queued), atomic_read(&n_clone_dropped),
#endif
                     (int)kr_clone_ns_ok,
                     atomic_read(&n_newmnt_seen), atomic_read(&n_newmnt_recorded),
                     atomic_read(&n_newmnt_pathfail), (int)kr_newmnt_ok,
                     n_mount_keep, atomic_read(&n_keep_rescans),
                     n_fdinfo_probes,
                     atomic_read(&n_fdinfo_entry), atomic_read(&n_fdinfo_hits),
                     atomic_read(&n_fdinfo_rewrites),
                     atomic_read(&n_fdinfo_nolabel),
                     atomic_read(&n_statx_entry), atomic_read(&n_statx_ret),
                     atomic_read(&n_statx_hits), atomic_read(&n_statx_rewrites),
                     atomic_read(&n_statx_nobuf), atomic_read(&n_statx_err),
                     atomic_read(&n_statx_copyfail), atomic_read(&n_statx_nomap),
                     (int)kr_statx_ok, (int)kr_statx_do_ok);
}
static const struct kernel_param_ops sus_mount_stat_ops = {
    .get = sus_mount_stat_show,
};
module_param_cb(mount_stat, &sus_mount_stat_ops, NULL, 0400);

static int sus_mount_show_pre(struct kprobe *kp, struct pt_regs *regs)
{
    struct vfsmount *mnt = (struct vfsmount *)regs->regs[1];
    struct mount *r;

    if (!susfs_ptr_plausible(mnt))
        return 0;
    r = real_mount(mnt);

    if (!sus_mount_is_ours(r)) {

        sus_mount_idmap_drop((int)r->mnt_id);

        if (mount_dbg && atomic_inc_return(&n_dbg_logged) <= 40)
            SUSFS_LOGI("sus_mount: hook: NOT ours id=%d s_dev=%u root=%px devname=%s\n",
                    r->mnt_id, (unsigned int)r->mnt.mnt_sb->s_dev,
                    r->mnt.mnt_root, r->mnt_devname ? r->mnt_devname : "none");
        return 0;
    }

    if (sus_mount_is_su_domain())
        return 0;
    sus_mount_note_id(r);
    atomic_inc(&n_ident_hits);
    regs->pc = regs->regs[30];   /* skip this mount line */

    regs->regs[0] = 0;
    return 1;
}

static struct kprobe kp_vfsstat = {
    .symbol_name = "show_vfsstat",
    .pre_handler = sus_mount_show_pre,
};

static struct kprobe kp_mountinfo = {
    .symbol_name = "show_mountinfo",
    .pre_handler = sus_mount_show_pre,
};

static struct kprobe kp_vfsmnt = {
    .symbol_name = "show_vfsmnt",
    .pre_handler = sus_mount_show_pre,
};

#define SUS_MOUNT_SHOW_N 3
static struct kprobe *const sus_mount_show_probes[SUS_MOUNT_SHOW_N] = {
    &kp_vfsstat, &kp_mountinfo, &kp_vfsmnt,
};
static const char *const sus_mount_show_names[SUS_MOUNT_SHOW_N] = {
    "show_vfsstat", "show_mountinfo", "show_vfsmnt",
};
static bool sus_mount_show_armed[SUS_MOUNT_SHOW_N];

/* Interrupt/kprobe safe: read-only, no allocation. */
static bool sus_mount_path_is_ours(const char *s)
{
    unsigned long flags;
    bool hit = false;
    int i;

    if (!s)
        return false;

    spin_lock_irqsave(&mount_keep_lock, flags);
    for (i = 0; i < n_mount_keep; i++) {
        size_t len = strlen(mount_keep[i]);

        if (len && !strncmp(s, mount_keep[i], len)) {
            hit = true;
            break;
        }
    }
    spin_unlock_irqrestore(&mount_keep_lock, flags);
    return hit;
}

#define SUS_MOUNT_ID_BATCH 8

/* ---- control surface: which mounts are ours ---- */

static int sus_mount_mark_ksu_mounts(void);	/* changing the list rescans */

static int sus_mount_keep_parse(const char *val, char dst[][SUS_MOUNT_KEEP_LEN], int max)
{
	char buf[SUS_MOUNT_KEEP_CMDLINE];
	const char *p;
	int n = 0;

	strscpy(buf, val, sizeof(buf));
	p = buf;
	while (*p) {
		char *tok;
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
		if (len >= SUS_MOUNT_KEEP_LEN)
			return -ENAMETOOLONG;
		if (n >= max)
			return -ENOSPC;
		memcpy(dst[n], tok, len);
		dst[n][len] = '\0';
		n++;
	}
	return n;
}

static void sus_mount_keep_commit(char dst[][SUS_MOUNT_KEEP_LEN], int n)
{
	unsigned long flags;

	spin_lock_irqsave(&mount_keep_lock, flags);
	memset(mount_keep, 0, sizeof(mount_keep));
	memcpy(mount_keep, dst, (size_t)n * SUS_MOUNT_KEEP_LEN);
	n_mount_keep = n;
	spin_unlock_irqrestore(&mount_keep_lock, flags);
}

static void sus_mount_keep_rescan(void)
{
	int rc;

	if (!mount_registered)
		return;		/* nothing is armed yet; the scan at enable will do it */
	rc = sus_mount_mark_ksu_mounts();
	atomic_inc(&n_keep_rescans);
	SUSFS_LOGI("sus_mount: rescanned after a list change: %d mount(s) marked (rc=%d)\n",
			rc, rc < 0 ? rc : 0);
}

static int sus_mount_keep_command(const char *val, bool bare_list)
{
	char *cmd;
	char (*staged)[SUS_MOUNT_KEEP_LEN];
	const char *arg;
	int i, n;
	int rc = 0;

	cmd = kvmalloc(SUS_MOUNT_KEEP_CMDLINE, GFP_KERNEL);
	staged = kvmalloc_array(SUS_MOUNT_KEEP_MAX, SUS_MOUNT_KEEP_LEN, GFP_KERNEL);
	if (!cmd || !staged) {
		kvfree(cmd);
		kvfree(staged);
		return -ENOMEM;
	}

	strscpy(cmd, val, SUS_MOUNT_KEEP_CMDLINE);
	for (i = (int)strlen(cmd) - 1; i >= 0 && (cmd[i] == '\n' || cmd[i] == '\r' || cmd[i] == ' '); i--)
		cmd[i] = '\0';

	if (!strcmp(cmd, "reset")) {
		strscpy(staged[0], mount_keep_default, SUS_MOUNT_KEEP_LEN);
		sus_mount_keep_commit(staged, 1);
		sus_mount_keep_rescan();
		SUSFS_LOGI("sus_mount: prefix list reset to the default\n");
		goto out;
	}
	if (!strcmp(cmd, "clear")) {
		sus_mount_keep_commit(staged, 0);
		SUSFS_LOGI("sus_mount: prefix list cleared (no new mount is accepted by path)\n");
		goto out;
	}
	if (!strncmp(cmd, "set ", 4)) {
		n = sus_mount_keep_parse(cmd + 4, staged, SUS_MOUNT_KEEP_MAX);
		if (n < 0) {
			rc = n;
			goto out;
		}
		sus_mount_keep_commit(staged, n);
		sus_mount_keep_rescan();
		SUSFS_LOGI("sus_mount: prefix list set to %d entr(ies)\n", n);
		goto out;
	}
	if (!strncmp(cmd, "add ", 4) || !strncmp(cmd, "del ", 4)) {
		bool adding = (cmd[0] == 'a');

		arg = cmd + 4;
		while (*arg == ' ')
			arg++;
		if (!*arg || strlen(arg) >= SUS_MOUNT_KEEP_LEN) {
			rc = -EINVAL;
			goto out;
		}

		spin_lock(&mount_keep_lock);
		n = n_mount_keep;
		if (n > SUS_MOUNT_KEEP_MAX)
			n = SUS_MOUNT_KEEP_MAX;
		memcpy(staged, mount_keep, (size_t)n * SUS_MOUNT_KEEP_LEN);
		spin_unlock(&mount_keep_lock);

		{
			bool found = false;

			for (i = 0; i < n; i++) {
				if (strcmp(staged[i], arg))
					continue;
				found = true;
				if (adding)
					goto out;
				memmove(&staged[i], &staged[i + 1],
					(size_t)(n - i - 1) * SUS_MOUNT_KEEP_LEN);
				n--;
				break;
			}
			if (adding) {
				if (found)
					goto out;
				if (n >= SUS_MOUNT_KEEP_MAX) {
					rc = -ENOSPC;
					goto out;
				}
				strscpy(staged[n], arg, SUS_MOUNT_KEEP_LEN);
				n++;
			} else if (!found) {
				rc = -ENOENT;
				goto out;
			}
		}
		sus_mount_keep_commit(staged, n);
		sus_mount_keep_rescan();
		SUSFS_LOGI("sus_mount: %s %s -> %d prefix(es)\n", adding ? "add" : "del", arg, n);
		goto out;
	}

	if (!bare_list) {
		rc = -EINVAL;
		goto out;
	}
	n = sus_mount_keep_parse(cmd, staged, SUS_MOUNT_KEEP_MAX);
	if (n < 0) {
		rc = n;
		goto out;
	}
	sus_mount_keep_commit(staged, n);
	sus_mount_keep_rescan();
	SUSFS_LOGI("sus_mount: prefix list set to %d entr(ies)\n", n);

out:
	kvfree(staged);
	kvfree(cmd);
	return rc;
}

static int sus_mount_keep_format(char *buf, size_t size)
{
	int n = 0;
	int i;

	n += scnprintf(buf + n, size - n,
		"mount prefixes: %d/%d, rescans=%d, recorded=%d, hidden_by_identity=%d, learned_ids=%d\n",
		n_mount_keep, SUS_MOUNT_KEEP_MAX, atomic_read(&n_keep_rescans),
		atomic_read(&n_newmnt_recorded), atomic_read(&n_ident_hits),
		atomic_read(&n_ident_learned));
	n += scnprintf(buf + n, size - n, "prefixes:");
	for (i = 0; i < n_mount_keep && n < (int)size - 64; i++)
		n += scnprintf(buf + n, size - n, " %s", mount_keep[i]);
	if (!n_mount_keep)
		n += scnprintf(buf + n, size - n, " (none - only KSU-range ids are hidden)");
	n += scnprintf(buf + n, size - n, "\n");
	return n;
}

/* ---- insmod parameters must not touch the guard-protected side ----
 * module_param_cb()'s setter runs during load_module()'s parse_args(), i.e. BEFORE susfs_init() has
 * reached susfs_imports_guard() and before this layer is up.  sus_mount_keep_command() is not
 * import-free: committing the list takes spin_lock_irqsave(&mount_keep_lock) and the rescan walks
 * the mount namespace - and _raw_spin_lock_irqsave is one of the imports the guard's table covers
 * (imports_guard.c), so a loader that left it at zero jumped to address 0 before anything could
 * refuse the load.  The setter validates the shape and caches the raw value instead, and
 * susfs_sus_mount_init() applies it through the same entry point once the guard has passed.
 * mount_keep_ready marks the point after which the setter applies live, and sus_mount_keep_param_lock
 * orders "cache" against "apply" (a commit replaces the list, so a write landing between
 * "ready = true" and the cached apply must not be clobbered by the older value).  (That table is not
 * the whole import set: ordinary exports such as strscpy/kvmalloc are the loader's and the
 * build-time System.map gate's business, which is why the validation below may use them.)
 *
 * mutex_lock/mutex_unlock - in that table as well - are still reached from the pre-guard window on
 * purpose, and that is not removable by a local change: the mutex is what orders the cache against
 * the apply, and the other mutual-exclusion primitives available here (_raw_spin_lock*,
 * __rcu_read_*) are in the same table.  Closing it needs a lock-free publication of the cached value
 * (store, re-check the ready flag, apply live). */
static char mount_keep_pending[SUS_MOUNT_KEEP_CMDLINE];
static bool mount_keep_pending_given;
static bool mount_keep_ready;
static DEFINE_MUTEX(sus_mount_keep_param_lock);

/* Validation only, through the same parser the command uses, so the limits and the error codes
 * cannot drift.  No lock, no commit, no rescan - safe to call from parse_args(). */
static int sus_mount_keep_list_check(const char *list)
{
	char (*dst)[SUS_MOUNT_KEEP_LEN];
	int rc;

	dst = kvmalloc_array(SUS_MOUNT_KEEP_MAX, SUS_MOUNT_KEEP_LEN, GFP_KERNEL);
	if (!dst)
		return -ENOMEM;
	rc = sus_mount_keep_parse(list, dst, SUS_MOUNT_KEEP_MAX);
	kvfree(dst);
	return rc < 0 ? rc : 0;
}

/* The grammar sus_mount_keep_command() accepts, checked without running it: `reset`, `clear`,
 * `set <list>`, `add <prefix>`, `del <prefix>`, or - the insmod form - a bare list.  @val is
 * modified in place (trailing whitespace trimmed), which is why the caller hands over its own
 * copy. */
static int sus_mount_keep_check(char *val)
{
	const char *arg;
	size_t i;

	for (i = strlen(val); i > 0 && (val[i - 1] == '\n' || val[i - 1] == '\r' || val[i - 1] == ' '); i--)
		val[i - 1] = '\0';

	/* An empty value is not "set the list to nothing": that is what `clear` says, and silently
	 * emptying the prefix list (which the built-in default otherwise seeds) is not something a typo
	 * should do. */
	if (!val[0])
		return -EINVAL;
	if (!strcmp(val, "reset") || !strcmp(val, "clear"))
		return 0;
	if (!strncmp(val, "set ", 4))
		return sus_mount_keep_list_check(val + 4);
	if (!strncmp(val, "add ", 4) || !strncmp(val, "del ", 4)) {
		arg = val + 4;
		while (*arg == ' ')
			arg++;
		if (!*arg || strlen(arg) >= SUS_MOUNT_KEEP_LEN)
			return -EINVAL;
		/* parse_args() runs before the list has any entry, so `del` here could only fail later
		 * (-ENOENT, "not listed"). */
		if (val[0] == 'd')
			return -EINVAL;
		return 0;
	}
	return sus_mount_keep_list_check(val);
}

/* The same trailing-whitespace rule the command applies ("echo" leaves a "\n" behind), used to tell
 * an empty value from a real one on the live path as well. */
static bool sus_mount_keep_value_empty(const char *val)
{
	size_t i;

	for (i = strlen(val); i > 0; i--)
		if (val[i - 1] != '\n' && val[i - 1] != '\r' && val[i - 1] != ' ')
			return false;
	return true;
}

static int sus_mount_keep_param_set(const char *val, const struct kernel_param *kp)
{
	int rc;

	mutex_lock(&sus_mount_keep_param_lock);
	if (mount_keep_ready) {
		bool empty = sus_mount_keep_value_empty(val);
		bool too_long = strlen(val) >= SUS_MOUNT_KEEP_CMDLINE;

		mutex_unlock(&sus_mount_keep_param_lock);
		/* An empty value is not "set the list to nothing" - that is what `clear` says, and the
		 * pre-init path refuses it for the same reason (see sus_mount_keep_check()).  A value
		 * that does not fit the command buffer is refused too: its tail is cut off, and the cut
		 * can leave an empty command behind, i.e. the same silent clear. */
		return (empty || too_long) ? -EINVAL : sus_mount_keep_command(val, true);
	}

	/* parse_args(): validate and cache only - see mount_keep_pending.  Validate the value itself,
	 * not a copy that was already truncated to the cache size. */
	if (strlen(val) >= sizeof(mount_keep_pending)) {
		mutex_unlock(&sus_mount_keep_param_lock);
		return -EINVAL;
	}
	strscpy(mount_keep_pending, val, sizeof(mount_keep_pending));
	rc = sus_mount_keep_check(mount_keep_pending);
	if (!rc)
		mount_keep_pending_given = true;
	mutex_unlock(&sus_mount_keep_param_lock);
	return rc;
}

static int sus_mount_keep_param_get(char *buf, const struct kernel_param *kp)
{
	return sus_mount_keep_format(buf, PAGE_SIZE);
}

static const struct kernel_param_ops sus_mount_keep_ops = {
	.get = sus_mount_keep_param_get,
	.set = sus_mount_keep_param_set,
};
/* 0600: root only; the whole directory is inside the one hide_modules hides. */
module_param_cb(hide_mounts, &sus_mount_keep_ops, NULL, 0600);

static int sus_mount_keep_proc_show(struct seq_file *m, void *v)
{
	char buf[512];

	sus_mount_keep_format(buf, sizeof(buf));
	seq_puts(m, buf);
	return 0;
}

static int sus_mount_keep_proc_open(struct inode *inode, struct file *file)
{

	if (current_uid().val != 0)
		return -ENOENT;
	return single_open(file, sus_mount_keep_proc_show, NULL);
}

static ssize_t sus_mount_keep_proc_write(struct file *file, const char __user *buf,
					 size_t len, loff_t *off)
{
	char cmd[SUS_MOUNT_KEEP_CMDLINE];
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

	/* Commands only: a typo must not silently replace the list. */
	rc = sus_mount_keep_command(cmd, false);
	if (rc)
		return rc;
	return len;
}

static const struct proc_ops sus_mount_keep_proc_ops = {
	.proc_open = sus_mount_keep_proc_open,
	.proc_read = seq_read,
	.proc_write = sus_mount_keep_proc_write,
	.proc_lseek = seq_lseek,
	.proc_release = single_release,
};

static struct proc_dir_entry *sus_mount_keep_entry;

static int sus_mount_scan_ns(struct mnt_namespace *ns, char *buf, unsigned long min)
{
    int batch[SUS_MOUNT_ID_BATCH];
    int replaced[SUS_MOUNT_ID_BATCH];
    int n_batch = 0, used = 0, n_replaced = 0;
    SUS_MOUNT_ITER_TYPE pos;
    unsigned int seen = 0;
    int scan_logged = 0;
    int marked = 0;
    unsigned int n_devname = 0, n_dpath_ok = 0, n_dpath_err = 0;
    unsigned int n_skipped_ns = 0, n_skipped_marked = 0;
    bool hit_cap = false;
    bool failed = false;
    int i;

    if (!sus_mount_ns_walk_begin()) {
        pr_warn("sus_mount: namespace_sem could not be resolved at load time - refusing to walk ns %p without the lock the kernel's own mount-table iterator holds (mounts stay unmarked)\n",
                ns);
        return -ENOSYS;
    }

    for (i = 0; i < SUS_MOUNT_ID_BATCH; i++) {
        int id = sus_mount_ida_alloc();

        if (id < 0)
            break;
        if (id < (int)DEFAULT_KSU_MNT_ID) {

            sus_mount_ida_release(id);
            break;
        }
        batch[n_batch++] = id;
    }
    if (!n_batch) {
        pr_warn("sus_mount: could not allocate KSU-range ids for ns %p - that namespace is left unmarked\n",
                ns);
        sus_mount_ns_walk_end();
        return 0;
    }

    rcu_read_lock();
#if LINUX_VERSION_CODE < KERNEL_VERSION(6, 12, 0)
    spin_lock(&ns->ns_lock);
#endif
    SUS_MOUNT_ITER_FOR(ns, pos) {
        struct path mnt_path;
        struct mount *r;
        const char *shown;
        char *dp;
        int new_id;

        if (seen++ >= SUS_MOUNT_MAX_SCAN) {
            hit_cap = true;
            break;
        }
        r = SUS_MOUNT_ITER_MOUNT(pos);

        if (SUS_MOUNT_MNT_NOT_IN_NS(r, ns)) {
            n_skipped_ns++;
            continue;
        }

        if ((unsigned int)r->mnt_id >= SUS_MOUNT_KSU_ID_MIN) {
            n_skipped_marked++;
            sus_mount_idmap_add((int)r->mnt_id, sus_mount_shown_id(r), r->mnt.mnt_sb->s_dev);
            sus_mount_ident_add(r);
            continue;
        }

        if (sus_mount_path_is_ours(r->mnt_devname)) {
            n_devname++;
            shown = r->mnt_devname;
        } else {

            mnt_path.mnt = &r->mnt;
            mnt_path.dentry = r->mnt.mnt_root;
            dp = sus_mount_d_path(&mnt_path, buf, PATH_MAX);

            if (scan_logged < 40) {
                scan_logged++;
                SUSFS_LOGI("sus_mount: scan %s -> %s\n", r->mnt_devname,
                        IS_ERR_OR_NULL(dp) ? "(d_path failed)" : dp);
            }
            if (IS_ERR_OR_NULL(dp)) {
                n_dpath_err++;
                continue;
            }
            n_dpath_ok++;
            if (!sus_mount_path_is_ours(dp))
                continue;
            shown = dp;
        }

        if (used >= n_batch) {
            pr_warn("sus_mount: id batch exhausted in ns %p, remaining mounts left unmarked\n",
                    ns);
            failed = true;
            break;
        }
        new_id = batch[used++];
        SUSFS_LOGI("sus_mount: marked mnt_id %d -> %d (%s, devname %s)\n",
                r->mnt_id, new_id, shown,
                r->mnt_devname ? r->mnt_devname : "none");
        if (n_replaced < (int)ARRAY_SIZE(replaced))
            replaced[n_replaced++] = r->mnt_id;
        r->mnt_id = new_id;

        sus_mount_idmap_add(new_id, sus_mount_shown_id(r), r->mnt.mnt_sb->s_dev);

        sus_mount_ident_add(r);
        marked++;
    }
#if LINUX_VERSION_CODE < KERNEL_VERSION(6, 12, 0)
    spin_unlock(&ns->ns_lock);
#endif
    rcu_read_unlock();
    sus_mount_ns_walk_end();

    /* Hand back whatever the batch did not use. */
    for (i = used; i < n_batch; i++)
        sus_mount_ida_release(batch[i]);

    /* ... and the ids the marked mounts used to own: the kernel frees r->mnt_id at teardown,
     * which is now the new id, so without this the original id is lost for good. */
    for (i = 0; i < n_replaced; i++)
        sus_mount_ida_release(replaced[i]);

    if (hit_cap)
        pr_warn("sus_mount: walk of ns %p stopped after %u entries (cap %d), result may be incomplete\n",
                ns, seen, SUS_MOUNT_MAX_SCAN);
    if (failed)
        pr_warn("sus_mount: marking in ns %p stopped early, %d mount(s) marked\n",
                ns, marked);
    SUSFS_LOGI("sus_mount: ns %p: seen=%u devname_hits=%u dpath_ok=%u dpath_err=%u skipped(other ns/cursor)=%u skipped(already marked)=%u marked=%d ids_alloc=%d\n",
            ns, seen, n_devname, n_dpath_ok, n_dpath_err, n_skipped_ns,
            n_skipped_marked, marked, n_batch);
    return marked;
}

static int sus_mount_mark_ksu_mounts(void)
{
    char *buf;
    unsigned long min;
    int marked;

    if (!sus_mount_ida_ready()) {
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 18, 0)
        pr_warn("sus_mount: NOT marking: mnt_id_xa=%s __xa_alloc=%s __xa_erase=%s must all be supplied; min_mnt_id stays false, so the feature does nothing\n",
                sus_mount_xa_obj_src, sus_mount_xa_alloc_src, sus_mount_xa_erase_src);
#else
        pr_warn("sus_mount: NOT marking: mnt_id_ida=%d ida_alloc_range=%d ida_free=%d must all resolve; min_mnt_id stays false, so the feature does nothing\n",
                !!sus_mount_mnt_id_ida, !!pfn_ida_alloc_range, !!pfn_ida_free);
#endif
        return -ENOSYS;
    }

    if (!current->nsproxy || !current->nsproxy->mnt_ns) {
        pr_warn("sus_mount: current has no mnt_ns, cannot scan for KSU mounts\n");
        return -ENOENT;
    }

    /* clamp the tunable (a value of 0/1 would match every mount line). */
    if (param_min_mnt_id < SUS_MOUNT_MIN_SANE_MNT_ID) {
        pr_warn("sus_mount: min_mnt_id=%lu is below %d, clamping to %llu\n",
                param_min_mnt_id, SUS_MOUNT_MIN_SANE_MNT_ID, DEFAULT_KSU_MNT_ID);
        param_min_mnt_id = DEFAULT_KSU_MNT_ID;
    }
    min = sus_mount_min_mnt_id();

    buf = kmalloc(PATH_MAX, GFP_KERNEL);
    if (!buf) {
        pr_warn("sus_mount: kmalloc(PATH_MAX) failed, no KSU mount marked\n");
        return -ENOMEM;
    }

    marked = sus_mount_scan_ns(current->nsproxy->mnt_ns, buf, min);

    kfree(buf);

    if (marked > 0)
        SUSFS_LOGI("sus_mount: %d KSU mount(s) marked with real ids from the kernel's own mount-id allocator (>= %llu), %d identity record(s) cached\n",
                marked, DEFAULT_KSU_MNT_ID, READ_ONCE(n_ident));
    else if (marked < 0)
        SUSFS_LOGI("sus_mount: scan refused (%d), nothing marked - the reason is the pr_warn above\n",
                marked);
    else
        SUSFS_LOGI("sus_mount: 0 KSU mounts marked (nothing under /data/adb matched in this mnt ns, hide threshold %lu)\n",
                min);
    return marked;
}

int susfs_sus_mount_init(void)
{
    int err;

    pfn_security_cred_getsecid =
        (void *)find_kernel_symbol_exact("security_cred_getsecid");
    pfn_d_path = (void *)find_kernel_symbol_exact("d_path");
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 18, 0)

    void *loader_xa = (void *)&mnt_id_xa;
    void *loader_alloc = (void *)&__xa_alloc;
    void *loader_erase = (void *)&__xa_erase;

    sus_mount_mnt_id_xa = (struct xarray *)find_kernel_symbol_exact("mnt_id_xa");
    if (sus_mount_mnt_id_xa) {
        sus_mount_xa_obj_src = "kallsyms";
        if (loader_xa && loader_xa != (void *)sus_mount_mnt_id_xa)
            pr_warn("sus_mount: mnt_id_xa: kallsyms %px != loader %px\n",
                    sus_mount_mnt_id_xa, loader_xa);
    } else if (loader_xa) {
        sus_mount_mnt_id_xa = loader_xa;
        sus_mount_xa_obj_src = "loader";
    }

    pfn_xa_alloc = (void *)find_kernel_symbol_exact("__xa_alloc");
    if (pfn_xa_alloc) {
        sus_mount_xa_alloc_src = "kallsyms";
        if (loader_alloc && loader_alloc != (void *)pfn_xa_alloc)
            pr_warn("sus_mount: __xa_alloc: kallsyms %px != loader %px\n",
                    (void *)pfn_xa_alloc, loader_alloc);
    } else if (loader_alloc) {
        pfn_xa_alloc = loader_alloc;
        sus_mount_xa_alloc_src = "loader";
    }

    pfn_xa_erase = (void *)find_kernel_symbol_exact("__xa_erase");
    if (pfn_xa_erase) {
        sus_mount_xa_erase_src = "kallsyms";
        if (loader_erase && loader_erase != (void *)pfn_xa_erase)
            pr_warn("sus_mount: __xa_erase: kallsyms %px != loader %px\n",
                    (void *)pfn_xa_erase, loader_erase);
    } else if (loader_erase) {
        pfn_xa_erase = loader_erase;
        sus_mount_xa_erase_src = "loader";
    }
#else
    sus_mount_mnt_id_ida = (struct ida *)find_kernel_symbol_exact("mnt_id_ida");
    pfn_ida_alloc_range = (void *)find_kernel_symbol_exact("ida_alloc_range");
    pfn_ida_free = (void *)find_kernel_symbol_exact("ida_free");
#endif
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)

    sus_mount_namespace_sem = (struct rw_semaphore *)find_kernel_symbol_exact("namespace_sem");

    pfn_put_mnt_ns = (void *)find_kernel_symbol_exact("put_mnt_ns");
#endif

    err = security_secctx_to_secid(param_su_ctx, strlen(param_su_ctx), &su_sid);
    if (err) {
        pr_warn("sus_mount: secctx_to_secid(%s) failed %d\n", param_su_ctx, err);
        su_sid = 0;
    }

    if (param_min_mnt_id < SUS_MOUNT_MIN_SANE_MNT_ID) {
        pr_warn("sus_mount: min_mnt_id=%lu is below %d, clamping to %llu\n",
                param_min_mnt_id, SUS_MOUNT_MIN_SANE_MNT_ID, DEFAULT_KSU_MNT_ID);
        param_min_mnt_id = DEFAULT_KSU_MNT_ID;
    }

    SUSFS_LOGI("sus_mount: su ctx \"%s\" -> sid %u (stock KernelSU uses \"u:r:su:s0\", override with susfs_guard_lkm.su_ctx)\n",
            param_su_ctx, su_sid);
    if (!pfn_security_cred_getsecid)
        pr_warn("sus_mount: security_cred_getsecid not found - no su-domain gating, KSU mounts will be hidden from EVERY process including su\n");
    if (!pfn_d_path)
        pr_warn("sus_mount: d_path not found - only mnt_devname is checked, meta-overlayfs style mounts will NOT be marked\n");

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 18, 0)
    SUSFS_LOGI("sus_mount: 6.18 mount-id allocator: mnt_id_xa via %s, __xa_alloc via %s, __xa_erase via %s\n",
            sus_mount_xa_obj_src, sus_mount_xa_alloc_src, sus_mount_xa_erase_src);
    if (!sus_mount_mnt_id_xa)
        pr_warn("sus_mount: mnt_id_xa not supplied (neither kallsyms nor the loader has the name) - KSU mounts will NOT be marked, threshold stays false (feature does nothing)\n");
    if (!pfn_xa_alloc)
        pr_warn("sus_mount: __xa_alloc not supplied - KSU mounts will NOT be marked, threshold stays false (feature does nothing)\n");
    if (!pfn_xa_erase)
        pr_warn("sus_mount: __xa_erase not supplied - KSU mounts will NOT be marked, threshold stays false (feature does nothing)\n");
#else
    if (!sus_mount_mnt_id_ida)
        pr_warn("sus_mount: mnt_id_ida not found - KSU mounts will NOT be marked, threshold stays false (feature does nothing)\n");
    if (!pfn_ida_alloc_range)
        pr_warn("sus_mount: ida_alloc_range not found - KSU mounts will NOT be marked, threshold stays false (feature does nothing)\n");
    if (!pfn_ida_free)
        pr_warn("sus_mount: ida_free not found - KSU mounts will NOT be marked, threshold stays false (feature does nothing)\n");
#endif
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
    if (!sus_mount_namespace_sem)
        pr_warn("sus_mount: namespace_sem not found - the namespace scan will refuse to walk, so KSU mounts will NOT be marked (feature does nothing)\n");
    if (!pfn_put_mnt_ns)
        pr_warn("sus_mount: put_mnt_ns not found - a namespace cloned after the enable is not recorded, so its mounts' ids are only learned by a later scan\n");
#endif

    SUSFS_LOGI("sus_mount: disabled by default (enable via CMD_SUSFS_HIDE_SUS_MNTS_FOR_NON_SU_PROCS)\n");

    {
        char staged[SUS_MOUNT_KEEP_MAX][SUS_MOUNT_KEEP_LEN] = { { 0 } };

        strscpy(staged[0], mount_keep_default, SUS_MOUNT_KEEP_LEN);
        sus_mount_keep_commit(staged, 1);
    }

    (void)sus_mount_mark_ksu_mounts();

    if (susfs_control_node_allowed()) {
        sus_mount_keep_entry = proc_create("susfs_hide_mounts", 0777, NULL,
                           &sus_mount_keep_proc_ops);
        if (!sus_mount_keep_entry)
            pr_warn("sus_mount: proc_create(susfs_hide_mounts) failed - runtime prefix control unavailable, use the hide_mounts parameter\n");
    } else {
        SUSFS_LOGI("sus_mount: /proc/susfs_hide_mounts not created (expose_proc=%d lsm=%d)\n",
                (int)susfs_expose_proc, (int)sus_path_lsm_active());
    }

    /* Apply what the insmod parameter cached (see mount_keep_pending): the import guard has passed
     * and this layer is up.  Applied AFTER the default seed above on purpose - an explicit
     * hide_mounts=<list> is what the operator asked for, instead of being silently replaced by the
     * built-in default (the same shape as hide_modules in susfs_hide_syms.c).  From here on the
     * setter applies live. */
    mutex_lock(&sus_mount_keep_param_lock);
    mount_keep_ready = true;
    if (mount_keep_pending_given) {
        int rc = sus_mount_keep_command(mount_keep_pending, true);

        if (rc)
            pr_warn("sus_mount: applying hide_mounts=\"%s\" from insmod failed %d - that prefix list is not in effect\n",
                    mount_keep_pending, rc);
    }
    mutex_unlock(&sus_mount_keep_param_lock);
    return 0;
}

static void sus_mount_unregister(void)
{
    int i;

    mutex_lock(&sus_mount_ctl_lock);
    if (!mount_registered) {
        mutex_unlock(&sus_mount_ctl_lock);
        return;
    }

    for (i = 0; i < SUS_MOUNT_SHOW_N; i++) {
        if (!sus_mount_show_armed[i])
            continue;
        unregister_kprobe(sus_mount_show_probes[i]);
        sus_mount_show_armed[i] = false;
    }
    n_show_probes = 0;
    if (kr_fdinfo_ok)
        sus_mount_fdinfo_disarm();
    if (kr_statx_ok) {
        unregister_kretprobe(&kr_statx);
        kr_statx_ok = false;
    }
    if (kr_statx_do_ok) {
        unregister_kretprobe(&kr_statx_do);
        kr_statx_do_ok = false;
    }
    if (kp_sb_down_ok) {
        unregister_kprobe(&kp_sb_down);
        kp_sb_down_ok = false;
    }
    if (kr_clone_ns_ok) {
        unregister_kretprobe(&kr_clone_ns);
        kr_clone_ns_ok = false;
    }
    if (kr_newmnt_ok) {
        unregister_kretprobe(&kr_newmnt);
        kr_newmnt_ok = false;
    }
    mount_registered = false;
    mutex_unlock(&sus_mount_ctl_lock);
}

void susfs_sus_mount_exit(void)
{
    unsigned long flags;

    if (sus_mount_keep_entry) {
        proc_remove(sus_mount_keep_entry);
        sus_mount_keep_entry = NULL;
    }
    sus_mount_unregister();
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)

    sus_mount_learn_stop();
#endif

    WRITE_ONCE(n_ident, 0);

    spin_lock_irqsave(&idmap_lock, flags);
    memset(mount_idmap, 0, sizeof(mount_idmap));
    n_idmap = 0;
    spin_unlock_irqrestore(&idmap_lock, flags);
}

static int sus_mount_register(void)
{
    int rc, i;

    mutex_lock(&sus_mount_ctl_lock);
    if (mount_registered) {
        mutex_unlock(&sus_mount_ctl_lock);
        return 0;
    }

    for (i = 0; i < SUS_MOUNT_SHOW_N; i++) {
        rc = register_kprobe(sus_mount_show_probes[i]);
        if (rc) {
            pr_warn("sus_mount: register_kprobe(%s) failed %d - that file keeps showing our mounts\n",
                    sus_mount_show_names[i], rc);
            continue;
        }
        sus_mount_show_armed[i] = true;
        n_show_probes++;
    }
    if (!n_show_probes) {
        pr_err("sus_mount: none of show_vfsstat/show_mountinfo/show_vfsmnt could be hooked - not reporting the feature as enabled\n");
        mutex_unlock(&sus_mount_ctl_lock);
        return -EINVAL;
    }

    rc = sus_mount_fdinfo_arm();
    if (rc)
        pr_warn("sus_mount: the fdinfo probe could not be armed %d - /proc/<pid>/fdinfo keeps printing the real mnt_id\n", rc);
    rc = register_kretprobe(&kr_statx);
    if (rc) {
        pr_warn("sus_mount: register_kretprobe(__arm64_sys_statx) failed %d - statx keeps returning the real stx_mnt_id\n", rc);
    } else {
        kr_statx_ok = true;
    }
    rc = register_kretprobe(&kr_statx_do);
    if (rc) {
        pr_warn("sus_mount: register_kretprobe(do_statx) failed %d - the second statx landing point is not armed\n", rc);
    } else {
        kr_statx_do_ok = true;
    }

    rc = register_kprobe(&kp_sb_down);
    if (rc)
        pr_warn("sus_mount: register_kprobe(generic_shutdown_super) failed %d - records are NOT dropped when their filesystem is unmounted, a reused s_dev can match an unrelated mount\n",
                rc);
    else
        kp_sb_down_ok = true;

    rc = register_kretprobe(&kr_clone_ns);
    if (rc)
        pr_warn("sus_mount: register_kretprobe(copy_mnt_ns) failed %d - ids of mounts in a namespace copied later are only learned when its mount table is read\n",
                rc);
    else
        kr_clone_ns_ok = true;

    rc = register_kretprobe(&kr_newmnt);
    if (rc)
        pr_warn("sus_mount: register_kretprobe(attach_recursive_mnt) failed %d - a mount created after the enable is NOT hidden (not marked, no identity recorded)\n",
                rc);
    else
        kr_newmnt_ok = true;
    mount_registered = true;
    mutex_unlock(&sus_mount_ctl_lock);
    return 0;
}

/* supercall: CMD_SUSFS_HIDE_SUS_MNTS_FOR_NON_SU_PROCS */
void susfs_sus_mount_supercall(void __user **arg)
{
    struct st_susfs_hide_sus_mnts_for_non_su_procs info = {0};
    int rc;

    if (copy_from_user(&info, (void __user *)*arg, sizeof(info))) {
        info.err = -EFAULT;
        goto out;
    }

    if (info.enabled) {
        rc = sus_mount_register();
        if (rc) {
            info.err = rc;
            goto out;
        }

        rc = sus_mount_mark_ksu_mounts();
        if (rc < 0) {
            pr_warn("sus_mount: scan on enable failed %d - hook is live but no mount was marked, reporting the failure to userspace\n",
                    rc);
            info.err = rc;
            goto out;
        }
    } else if (mount_registered) {
        sus_mount_unregister();
    }
    info.err = 0;
    SUSFS_LOGI("sus_mount: %s (supercall)\n", info.enabled ? "hide" : "unhide");
out:
    /* upstream writes back only ->err for input-type commands */
    if (copy_to_user(&((struct st_susfs_hide_sus_mnts_for_non_su_procs __user *)*arg)->err,
                     &info.err, sizeof(info.err)))
        pr_warn("sus_mount supercall copy_to_user failed\n");
}
