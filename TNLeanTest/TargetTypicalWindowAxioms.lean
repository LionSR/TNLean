/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TargetTypicalWindow

/-! Stock foundational dependencies of the actual target typical-window construction. -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.Scan.ScannerExponents.one_le_L_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.ScannerExponents.one_le_L_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.source_target_geometry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.source_target_geometry

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.target_typicalSet_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.target_typicalSet_bounds

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_truncated_target_typical_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_truncated_target_typical_window

/-- info: 'Entropy.exists_typical_tail_bound_of_log_pow_twelve_budget'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.exists_typical_tail_bound_of_log_pow_twelve_budget
