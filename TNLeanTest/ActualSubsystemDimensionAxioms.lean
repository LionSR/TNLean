/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SubsystemDimensionScale

/-! # Axiom audit for actual physical subsystem dimensions -/

set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan TNLean.PEPS.AreaLaw.Scan.CollarScan

/-- info: 'TNLean.PEPS.AreaLaw.Scan.card_domainGraph_ball_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms card_domainGraph_ball_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.card_fill_moved_le_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms card_fill_moved_le_one

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.card_chargeStep_moved_le_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms card_chargeStep_moved_le_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.designatedSupport_eq_ball_of_state_not_constant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designatedSupport_eq_ball_of_state_not_constant

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.designatedSupport_eq_ball_of_old_not_constant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designatedSupport_eq_ball_of_old_not_constant

/-- info: 'TNLean.PEPS.AreaLaw.Scan.prod_physical_subsystem_dimension'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prod_physical_subsystem_dimension

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.log_chargeStep_moved_dimension_le_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms log_chargeStep_moved_dimension_le_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.log_designatedSupport_dimension_le_of_state_not_constant_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms log_designatedSupport_dimension_le_of_state_not_constant_domainGraph

/-- info: 'TNLean.PEPS.AreaLaw.Scan.transportLogDimBound_roundedLogRadius_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transportLogDimBound_roundedLogRadius_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.eventually_transportLogDimBound_roundedLogRadius_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_transportLogDimBound_roundedLogRadius_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.exists_transportLogDimBound_log_four'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_transportLogDimBound_log_four

/-- info: 'TNLean.PEPS.AreaLaw.Scan.exists_transportCoefficients_log_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_transportCoefficients_log_bound

/-- info: 'TNLean.PEPS.AreaLaw.Scan.transportLogDimBound_le_radius_sq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transportLogDimBound_le_radius_sq

/-- info: 'TNLean.PEPS.AreaLaw.Scan.mul_transportLogDimBound_le_of_radius_small'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_transportLogDimBound_le_of_radius_small

/-- info: 'TNLean.PEPS.AreaLaw.Scan.exists_pos_radius_smallness_threshold'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_pos_radius_smallness_threshold
