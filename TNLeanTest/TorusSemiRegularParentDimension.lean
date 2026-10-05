/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusSemiRegularParentDimension

/-! # Full native parent dimension with arbitrary semi-regular multiplicities -/
set_option linter.hashCommand false
open TNLean.PEPS

example {w h : ℕ} [NeZero w] [NeZero h] [Fact (2 < w)] [Fact (2 < h)]
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] {p : ℕ}
    {U : G →* Matrix X X ℂ} {a : X → X → X → X → Fin p → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    Module.finrank ℂ (regionParentGroundSpace
      (groupBondTensor (torusNativeIncidentSite (width := w) (height := h) a))
      torusPlaquetteRegion) = Nat.card (CommutingPairConjugacyClass G) :=
  ha.finrank_torusParentGroundSpace_of_isSemiRegular hU hSemi

/--
info: 'TNLean.PEPS.IsGInjective.finrank_torusParentGroundSpace_of_isSemiRegular'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.PEPS.IsGInjective.finrank_torusParentGroundSpace_of_isSemiRegular
/--
info: 'TNLean.PEPS.IsGInjective.finrank_torusParentKernel_of_isSemiRegular'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.PEPS.IsGInjective.finrank_torusParentKernel_of_isSemiRegular
