/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.NestedPatches

/-! # Standard kernel-dependency guards for the nested-square geometry -/

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.card_edgeBoundary_closedSquareSample_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.card_edgeBoundary_closedSquareSample_le

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.abs_squareRadius_sub_le_one_of_adj'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.abs_squareRadius_sub_le_one_of_adj

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.mem_edgeBoundary_closedSquareSample_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.mem_edgeBoundary_closedSquareSample_iff

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.card_closedSquareSample_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.card_closedSquareSample_le

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.card_closedSquareSample_le_eightyOne'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.card_closedSquareSample_le_eightyOne

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.nestedPatchRadius_le_two_mul'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.nestedPatchRadius_le_two_mul

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.nestedPatch_crossing_disjoint_earlier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.nestedPatch_crossing_disjoint_earlier

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.nestedPatch_crossing_subset_later'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.nestedPatch_crossing_subset_later

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.nestedPatch_crossing_unique'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.nestedPatch_crossing_unique

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.disjoint_edgeBoundary_nestedPatch'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.disjoint_edgeBoundary_nestedPatch

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.card_edgeBoundary_nestedPatch_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.card_edgeBoundary_nestedPatch_le

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.nestedPatch_quadratic_budget'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.nestedPatch_quadratic_budget

/-- info: 'TNLean.PEPS.AreaLaw.Geometry.sum_card_edgeBoundary_nestedPatch_mul_sq_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.sum_card_edgeBoundary_nestedPatch_mul_sq_le
