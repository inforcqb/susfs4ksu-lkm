// SPDX-License-Identifier: GPL-2.0

/* issue #34: the hide gates ask KernelSU whether it would umount modules for a uid, instead of the
 * old `uid >= 10000` proxy that hid from the manager and from su-granted apps too.
 *
 * Which environment loaded this module is the LOADER's business, not this module's: it either
 * resolves ksu_uid_should_umount() from kallsyms (KernelSU present) or pins it to 0 and passes
 * `is_magisk=1` (a device with no KernelSU hint: Magisk, APatch - see tools/susfs_insmod.c).  All
 * this file does with that parameter is set the one flag the gates read, so such a load never calls
 * the symbol - which is what makes a pinned 0 safe, and what a wrong parameter would break.
 *
 * Hence the refusal below, and hence it is FATAL.  The loader is responsible for the other half: it
 * stands in for the symbol only when neither of its two KernelSU hints says so (the loader's own
 * domain is u:r:ksu*, or /sys/module/kernelsu exists), and leaves it unresolved - a loud "Unknown
 * symbol" refusal - when a hint does say so but the symbol is missing; tools/susfs_insmod.c also
 * records that some KernelSU builds hide that directory.  What this layer refuses is the remaining
 * combination - is_magisk unset, the symbol not in kallsyms, no loader that vouched for either -
 * where the only answers left are calling a zero address or silently hiding from nobody.  A plain
 * `insmod` cannot get this far anyway: it cannot absolutize any of this module's ~95 unexported
 * imports.
 *
 * Known residual, accepted: a third-party loader that writes 0 into this name while the kernel's
 * own kallsyms does have it would pass the check below and be called.  The loader this repository
 * ships is self-consistent - it pins only a name it could not resolve, and the kptr_restrict guard
 * ahead of that refuses the whole image when every address reads as zero - so the combination needs
 * a loader that does not exist here; ksud's behaviour was not verifiable.  The structural fix would
 * be resolving the address at run time instead of importing the name. */

#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/moduleparam.h>
#include <linux/types.h>

#include "ksu_umount_gate.h"
#include "symbol_resolver.h"
#include "susfs_log.h"

#define KSU_UMOUNT_GATE_SYMBOL	"ksu_uid_should_umount"

bool susfs_ksu_umount_gate_off;

/* Written by the loader, read here once.  0444 on purpose: this is a fact about the device the
 * module was loaded on, not a runtime switch - a later write must not turn the gates into calls to
 * a pinned zero. */
static bool is_magisk;
module_param(is_magisk, bool, 0444);

int susfs_ksu_umount_gate_init(void)
{
	if (is_magisk) {
		susfs_ksu_umount_gate_off = true;
		/* pr_warn, not SUSFS_LOGI: "#34's fix is not in effect on this device" is a fact an
		 * operator has to be able to see, and the load is otherwise silent about it. */
		pr_warn("susfs_guard_lkm: is_magisk=1 (passed by the loader) - KernelSU's ksu_uid_should_umount is never asked, so the hide gates keep the uid >= 10000 rule and issue #34's fix (hiding follows KernelSU's exclusion list) is NOT in effect here\n");
		return 0;
	}

	/* is_magisk unset: the loader is claiming KernelSU.  Confirm the symbol is there before any
	 * gate can be reached, because a loader that passed nothing was not asked to pin it either.
	 * ksu_kallsyms_lookup_name() is the bootstrapped kallsyms_lookup_name(), whose implementation
	 * ends in module_kallsyms_lookup_name() - a name owned by kernelsu.ko is found by it. */
	if (!ksu_kallsyms_lookup_name(KSU_UMOUNT_GATE_SYMBOL)) {
		pr_err("susfs_guard_lkm: neither is_magisk=1 nor KernelSU's %s is present - refusing to load rather than hiding from nobody or calling a zero address. On a device without KernelSU, load with `susfs_insmod`, which passes is_magisk=1 itself.\n",
		       KSU_UMOUNT_GATE_SYMBOL);
		return -EINVAL;
	}

	SUSFS_LOGI("ksu_umount_gate: KernelSU's %s is present - the hide gates answer it (issue #34)\n",
		   KSU_UMOUNT_GATE_SYMBOL);

	return 0;
}
