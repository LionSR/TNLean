/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.StatusMarginalMoments
import TNLean.PEPS.AreaLaw.Scan.StatusScaleSeparation

/-! Foundational dependencies of the common physical marginal input. -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_statusMarginal_cutBudget_le_log'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_statusMarginal_cutBudget_le_log

/-- info: 'TNLean.PEPS.AreaLaw.Scan.tailRadius_antitone_budget'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.tailRadius_antitone_budget

/-- info: 'TNLean.PEPS.AreaLaw.Scan.tailRadius_eq_div_sqrt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.tailRadius_eq_div_sqrt

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.log_surprisalMoment_truncated_reducedState_le_common'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.PEPS.AreaLaw.Scan.CollarScan.log_surprisalMoment_truncated_reducedState_le_common

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_truncated_statusMarginal_moment_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_truncated_statusMarginal_moment_bounds

/-- info: 'TNLean.PEPS.AreaLaw.Scan.eventually_status_scale_separation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.eventually_status_scale_separation
