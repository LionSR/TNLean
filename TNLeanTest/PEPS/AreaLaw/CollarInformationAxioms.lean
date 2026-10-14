/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.CollarInformation

/-! # Expected kernel dependencies of the deterministic collar steps -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'FiniteProduct.collarLeaf_entropy_identity'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.collarLeaf_entropy_identity

/-- info:
'FiniteProduct.two_mutualInformation_le_collarLeaf'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.two_mutualInformation_le_collarLeaf

/-- info:
'FiniteProduct.two_mutualInformation_le_collarLeaf_average'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.two_mutualInformation_le_collarLeaf_average

/-- info:
'FiniteProduct.abs_mutualInformation_sub_le_of_traceDistance'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.abs_mutualInformation_sub_le_of_traceDistance

/-- info:
'FiniteProduct.mutualInformation_le_add_of_traceDistance_le_rpow'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.mutualInformation_le_add_of_traceDistance_le_rpow

/-- info:
'TNLean.PEPS.AreaLaw.Geometry.Template.collar_cut_card_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Geometry.Template.collar_cut_card_le

/-- info:
'TNLean.PEPS.AreaLaw.sublinearCollarBound_of_mutualInformation_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.sublinearCollarBound_of_mutualInformation_le
