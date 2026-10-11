/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialActiveRays

/-! Guarded kernel dependency reports for fan rays and actual initial frontiers. -/

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.cellFan_mem_radial_iff_sameRay_of_mem_closedBall'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.cellFan_mem_radial_iff_sameRay_of_mem_closedBall

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Geometry.initialRegion_frontier_small_closedBall_iff_active_ray'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.initialRegion_frontier_small_closedBall_iff_active_ray
