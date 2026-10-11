/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFanRays

/-! Guarded kernel dependency report for the restriction of a fan ray. -/

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.cellFan_mem_radial_iff_sameRay_of_mem_closedBall'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFan_mem_radial_iff_sameRay_of_mem_closedBall
