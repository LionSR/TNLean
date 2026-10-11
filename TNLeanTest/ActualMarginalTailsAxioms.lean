/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualMarginalTails

/-! Expected foundational dependencies of actual physical marginal tails. -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.cutBudget_eq_cutLogBudget'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.cutBudget_eq_cutLogBudget

/-- info: 'TNLean.PEPS.AreaLaw.cutBudget_compl'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.cutBudget_compl

/-- info: 'TNLean.PEPS.AreaLaw.one_le_cutBudget'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.one_le_cutBudget

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.log_surprisalMoment_truncated_reducedState_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.log_surprisalMoment_truncated_reducedState_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.surprisalTail_truncated_reducedState_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.surprisalTail_truncated_reducedState_le
