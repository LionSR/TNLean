/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialSectorAssignment

/-! Guarded kernel dependency report for the initial closed-half radius. -/

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.fineScaleIndex_closed_half_radius_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.fineScaleIndex_closed_half_radius_eq
