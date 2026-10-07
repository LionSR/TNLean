/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusSemiRegularParentGroundSpace

/-! # Native full-kernel semi-regular spanning regressions -/
noncomputable section
set_option linter.hashCommand false
open TNLean.PEPS

-- The final statement uses the actual closure vectors and positive parent terms.
example {w h : ℕ} [NeZero w] [NeZero h] [Fact (2 < w)] [Fact (2 < h)]
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] {p : ℕ}
    {U : G →* Matrix X X ℂ} {a : X → X → X → X → Fin p → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (P : (v : TorusVertex w h) → Matrix
      (RegionPhysicalConfig (d := p) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := p) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusNativeIncidentSite a))
      (torusPlaquetteRegion v) (P v)) :
    (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker =
      Submodule.span ℂ (Set.range (fun q : {q : G × G // Commute q.1 q.2} =>
        torusGClosure (width := w) (height := h) U a q.1.1 q.1.2)) :=
  ha.torusParentKernel_eq_commutingClosureSpan_of_isSemiRegular hU hSemi P hP

private instance : Fact (2 < 3) := ⟨by decide⟩

-- Two copies of the unique trivial-group irrep: multiplicity differs from its dimension.
example : ∃ (p : ℕ) (a : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin p → ℂ),
    IsGInjective (torusLegRep (1 : Unit →* Matrix (Fin 2) (Fin 2) ℂ)) (siteMap a) ∧
      Module.finrank ℂ (regionParentGroundSpace
        (groupBondTensor (torusNativeIncidentSite (width := 3) (height := 3) a))
        torusPlaquetteRegion) = Nat.card (CommutingPairConjugacyClass Unit) := by
  let U : Unit →* Matrix (Fin 2) (Fin 2) ℂ := 1
  have hs : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U) := by
    apply Representation.isSemiRegular_of_linearIndependent
    rw [linearIndependent_unique_iff]
    simp [U]
  obtain ⟨p, a, ha⟩ := exists_isGInjective_torusSite U
  exact ⟨p, a, ha, ha.finrank_torusParentGroundSpace_of_isSemiRegular
    (fun _ => by simp [U]) hs⟩

/--
info: 'TNLean.PEPS.IsGInjective.torusParentKernel_eq_commutingClosureSpan_of_isSemiRegular'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.PEPS.IsGInjective.torusParentKernel_eq_commutingClosureSpan_of_isSemiRegular
/--
info: 'TNLean.PEPS.IsGInjective.torusParentGroundSpace_eq_commutingClosureSpan_of_isSemiRegular'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.PEPS.IsGInjective.torusParentGroundSpace_eq_commutingClosureSpan_of_isSemiRegular
