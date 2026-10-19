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

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_truncated_reducedState_moment_tail_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_truncated_reducedState_moment_tail_bounds

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.truncated_reducedState_moment_tail_bounds_of_locality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open TNLean.PEPS.AreaLaw.Scan.CollarScan in
#print axioms truncated_reducedState_moment_tail_bounds_of_locality

/-- info: 'TNLean.PEPS.AreaLaw.positiveQuasilocalConstraints_explicit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.positiveQuasilocalConstraints_explicit

/-- info: 'TNLean.PEPS.AreaLaw.norm_latticePositiveConstraint_sub_map_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.norm_latticePositiveConstraint_sub_map_le

/-- info: 'TNLean.PEPS.AreaLaw.latticePositiveConstraints_explicit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.latticePositiveConstraints_explicit

/-- info: 'TNLean.PEPS.AreaLaw.latticeFiniteSetTruncation_explicit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.latticeFiniteSetTruncation_explicit

/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.truncated_reducedState_moment_tail_bounds_explicit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open TNLean.PEPS.AreaLaw.Scan.CollarScan in
#print axioms truncated_reducedState_moment_tail_bounds_explicit
