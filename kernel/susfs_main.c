// SPDX-License-Identifier: GPL-2.0
/*
 * susfs_main.c - SUSFS LKM entry point: the layer table plus this module's control nodes.
 * Loaded via `ksud insmod`, with unexported symbols relocated via kallsyms.
 */
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>

#include "symbol_resolver.h"
#include "susfs_log.h"
#include "lsm_hook.h"
#include "susfs.h"

/* The module's own name lives in susfs.h (SUSFS_LKM_MODULE_NAME / SUSFS_LKM_SYSFS_DIR):
 * /sys/module's directory and the rules that hide it (susfs_hide_syms.c) must agree, and the
 * version lives there as well (SUSFS_LKM_VERSION) because the load-time guard can refuse the
 * module before this file's banner runs. */

/* The /proc/susfs_* control nodes are created by default and are 0777 on purpose.
 * Measured on device, 0600 plus sus_path hiding does not work: `ls -l /proc/susfs_kstat`
 * -> ENOENT (the inode_getattr hook fired) but `cat` -> Permission denied (it did not), with
 * sus_path's perm counter stuck at 0 - inode_permission() runs the DAC check BEFORE
 * security_inode_permission(), so a 0600 root-owned node fails DAC first, the LSM hook is
 * never reached, and EACCES advertises that the node exists.  General to sus_path's path
 * layer: it can only turn an ENOENT-shaped answer out of files DAC would have ALLOWED.
 * Hence 0777: DAC passes, the LSM layer is the only thing that answers (ENOENT for every
 * non-root caller).
 * The nodes exist only when the layer that hides them is installed
 * (susfs_control_node_allowed()), so an unprotected world-writable node cannot happen, and
 * root-only access is enforced by the handlers' uid checks, not by the mode.  expose_proc=0
 * removes the nodes entirely. */
bool susfs_expose_proc = true;
module_param_named(expose_proc, susfs_expose_proc, bool, 0600);

static const char *const susfs_self_hide_paths[] = {
    "/proc/susfs_kstat",
    "/proc/susfs_open_redirect",
    "/proc/susfs_enable_log",
    "/proc/susfs_avc_spoof",
    SUSFS_HIDE_MODULES_NODE,
    SUSFS_HIDE_MOUNTS_NODE,
    /* sus_path's own interface (the rule listing): it goes through the same table it
     * prints, so a broken rule table is visible in the very view that reports it. */
    SUSFS_PATH_NODE,
    /* The module's own sysfs directory is NOT here: it belongs to hide_module
     * (susfs_hide_syms.c), which adds and drops that rule at runtime. */
};

/* Register our control nodes in sus_path's hidden set: probing them must answer ENOENT,
 * not EACCES.  Runs after every feature init (the nodes must exist for kern_path() to
 * resolve them) and after sus_path_init(), so the hooks are already patched. */
static void susfs_self_hide_nodes(void)
{
    int i;

    if (!susfs_expose_proc)
        return;

    for (i = 0; i < ARRAY_SIZE(susfs_self_hide_paths); i++) {
        int rc = sus_path_add_self_hidden(susfs_self_hide_paths[i]);

        if (rc)
            pr_warn("susfs_guard_lkm: self-hide %s failed %d\n",
                    susfs_self_hide_paths[i], rc);
    }
}

/* ---- layer table: arming order IS the teardown order, reversed --------------
 * A failed load must leave NOTHING armed: when module_init() returns an error the kernel
 * frees this module's memory, so anything still installed - a patched security_hook_heads
 * slot above all - becomes a function pointer into freed memory that the next syscall goes
 * through.  Hence the exits of the already-armed layers run before failing.
 * Teardown runs in the exact reverse of arming, in one place, and the order matters:
 * sus_path's LSM layer is what answers ENOENT for this module's own 0777 control nodes (see
 * the expose_proc note), so unhooking it before the nodes are removed would expose them to
 * every process during the unload - here the nodes go first and the LSM layer last.
 * `fatal` marks the two layers whose absence makes the module useless or silent: sus_path
 * and the supercall hook; the rest log their own failure and degrade to "off".  The exits
 * are idempotent, which lets one path serve rollback and unload alike. */
static int layer_lsm_hook_init(void)
{
    ksu_lsm_hook_init();
    return 0;
}

/* Not const: the `armed` flags live here (the pointers must outlive __init too). */
static struct {
    const char *name;
    int (*init)(void);
    void (*exit)(void);
    bool fatal;
    bool armed;			/* exit is run for every layer that was attempted */
} susfs_layers[] = {
    { "lsm_hook",	layer_lsm_hook_init,		ksu_lsm_hook_exit,	false, false },
    { "sus_path",	sus_path_init,			sus_path_exit,		true,  false },
    { "uname",		susfs_uname_init,		susfs_uname_exit,	false, false },
    { "kstat",		susfs_kstat_init,		susfs_kstat_exit,	false, false },
    { "sus_map",	susfs_sus_map_init,		susfs_sus_map_exit,	false, false },
    { "sus_mount",	susfs_sus_mount_init,		susfs_sus_mount_exit,	false, false },
    { "cmdline",	susfs_spoof_cmdline_init,	susfs_spoof_cmdline_exit, false, false },
    { "open_redirect",	susfs_open_redirect_init,	susfs_open_redirect_exit, false, false },
    { "enable_log",	susfs_enable_log_init,		susfs_enable_log_exit,	false, false },
    { "avc_spoof",	susfs_avc_spoof_init,		susfs_avc_spoof_exit,	false, false },
    { "supercall",	susfs_supercall_init,		susfs_supercall_exit,	true,  false },
    { "hide_syms",	susfs_hide_syms_init,		susfs_hide_syms_exit,	false, false },
};

/* Diagnostic: make one layer's init fail, by 1-based index, to exercise the rollback path
 * on the device - a `fatal` layer failing must leave the load with nothing armed. */
static int fail_layer;
module_param_named(fail_layer, fail_layer, int, 0644);

/* Not __init/__exit: it is called from both, and an __exit callee in __init code is a
 * modpost section mismatch. */
static void susfs_layers_down(int upto)
{
    int i;

    for (i = upto; i >= 0; i--) {
        if (!susfs_layers[i].armed)
            continue;
        susfs_layers[i].armed = false;
        if (susfs_layers[i].exit)
            susfs_layers[i].exit();
    }
}

static int __init susfs_init(void)
{
    int i;

    /* First, before any layer runs and while nothing is armed: an import that was not filled in
     * is an address this module would jump to on its first call through it.  See
     * imports_guard.c - a loader that continues after an unresolved name leaves it zero, which
     * the kernel accepts without a word. */
    if (susfs_imports_guard())
        return -EINVAL;

    SUSFS_LOGI("init v%s\n", SUSFS_LKM_VERSION);
    ksu_init_symbol_resolver();

    /* Now that kallsyms lookups work, check the addresses themselves: see imports_guard.c. */
    if (susfs_imports_crosscheck())
        return -EINVAL;

    for (i = 0; i < (int)ARRAY_SIZE(susfs_layers); i++) {
        int ret;

        /* Marked before the call: a layer that half-ran still has to be taken down. */
        susfs_layers[i].armed = true;

        if (fail_layer == i + 1) {
            pr_warn("susfs_guard_lkm: fail_layer=%d - forcing %s's init to fail (diagnostic)\n",
                    fail_layer, susfs_layers[i].name);
            ret = -EIO;
        } else {
            ret = susfs_layers[i].init ? susfs_layers[i].init() : 0;
        }

        if (!ret)
            continue;

        if (susfs_layers[i].fatal) {
            pr_err("susfs_guard_lkm: %s init failed %d, refusing to load\n",
                   susfs_layers[i].name, ret);
            /* The kernel is about to free this module; a hook left behind points into it. */
            susfs_layers_down(i);
            return ret;
        }
        pr_warn("susfs_guard_lkm: %s init failed %d - that feature stays off\n",
                susfs_layers[i].name, ret);
    }

    /* Registered last and undone implicitly: these are entries in sus_path's table, which
     * sus_path_exit() empties while its LSM layer still answers ENOENT for the nodes. */
    susfs_self_hide_nodes();

    /* Operator note.  The module hides its own traces from EVERY caller, root included (a
     * built-in SUSFS has no module entry, so hiding it only from non-root would leave a
     * trace upstream does not have): `lsmod | grep susfs` stays empty and a second `insmod`
     * fails with -EEXIST, which reads like a broken module.
     * THE ONE LINE THAT IGNORES THE LOG SWITCH: everything else follows enable_log
     * (susfs_log.h), but this is the only evidence the module came up and the one thing an
     * operator greps for, so it stays unconditional even for a silent load - otherwise
     * "loaded but logging off" is indistinguishable from "not loaded".  The prefix comes
     * from pr_fmt (susfs_log.h), so the message must not repeat it. */
    pr_info("loaded. This module is filtered out of /proc/modules for every caller including root, so `lsmod | grep susfs` stays empty - check /sys/module/%s instead (a second insmod fails with -EEXIST while it is loaded).\n",
            SUSFS_LKM_MODULE_NAME);

    return 0;
}

static void __exit susfs_exit(void)
{
    susfs_layers_down((int)ARRAY_SIZE(susfs_layers) - 1);
    SUSFS_LOGI("susfs_guard_lkm: exit\n");
}

module_init(susfs_init);
module_exit(susfs_exit);
MODULE_LICENSE("GPL");

/* The VFS symbol namespace of this kernel's GKI builds.
 *
 * Four symbols this module imports - kern_path and ihold (fs/), override_creds and
 * revert_creds (kernel/cred.c) - are exported as
 * EXPORT_SYMBOL_NS(sym, ANDROID_GKI_VFS_EXPORT_ONLY), and the Android build maps that
 * name to the long string below with a per-directory ccflag before the compiler
 * stringifies it (fs/Makefile: subdir-ccflags-y += -DANDROID_GKI_VFS_EXPORT_ONLY=...,
 * plus kernel/Makefile for cred.o on some releases).  A module that does not import the
 * RESULTING string is refused by the kernel's module loader with
 *   "module uses symbol (kern_path) from namespace VFS_internal_... but does not import
 *    it"  ->  "Unknown symbol kern_path (err -22)"
 * which is why plain insmod failed on the phone before this line existed.
 *
 * The long form must be written out literally: MODULE_IMPORT_NS(ns) stringifies its
 * argument, so passing the macro name ANDROID_GKI_VFS_EXPORT_ONLY would import a
 * namespace that no kernel ever creates.  (Measured on the built .ko: .modinfo carried
 * no import_ns entry at all.)
 *
 * Note this is necessary but NOT sufficient for plain insmod: nine further symbols we
 * reference are not in the kernel's export table in any of the six supported GKI
 * variants (kallsyms_lookup_name and friends, saved_boot_config, task_work_add, init_mm,
 * __set_fixmap, copy_to_kernel_nofault, dcache_clean_inval_poc), so loading without a
 * helper still needs those to be resolved at runtime.  The userspace loader
 * (tools/susfs_insmod.c) sidesteps the whole question by rewriting undefined symbols to
 * absolute addresses, exactly as KernelSU's ksud does - see README. */
MODULE_IMPORT_NS(VFS_internal_I_am_really_a_filesystem_and_am_NOT_a_driver);
MODULE_DESCRIPTION("SUSFS guard LKM (susfs_guard_lkm) v2.3.0-gki");
