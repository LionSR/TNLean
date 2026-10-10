/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.SafeRectangleDilation

/-! Kernel dependencies of the dilated-parent safety theorem. -/

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.IsSafe.of_subset_dilate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.IsSafe.of_subset_dilate
