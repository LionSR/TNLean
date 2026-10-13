/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadOldHistoryDecay

/-! # Expected kernel dependencies of the uniform old-history tail -/

set_option autoImplicit false

open Filter
open scoped BigOperators
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

set_option linter.hashCommand false

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_historyWeight_bad_old_le_bad_through'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_historyWeight_bad_old_le_bad_through

/-- info:
'TNLean.PEPS.AreaLaw.Scan.eventually_split_counting_scale_separation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.eventually_split_counting_scale_separation

/-- info:
'TNLean.PEPS.AreaLaw.Scan.exists_badOldHistory_threshold'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.exists_badOldHistory_threshold

