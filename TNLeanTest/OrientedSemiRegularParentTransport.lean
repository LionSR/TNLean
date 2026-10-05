/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.OrientedSemiRegularGInjectiveParentTransport
import TNLean.PEPS.TorusOrientedIncidentGInjectivity

/-! # Reversed-edge and native four-leg parent-transport regressions -/
noncomputable section
set_option linter.hashCommand false
open TNLean.PEPS
private abbrev Γ : SimpleGraph (Fin 2) := ⊤
private abbrev d : Fin 1 → ℕ := fun _ => 2
private abbrev m : Fin 1 → ℕ := fun _ => 3
private def eX (v : Fin 2) : (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin 2 :=
  (Fintype.equivFin _).trans (finCongr (by fin_cases v <;> decide))
private def eM (v : Fin 2) : (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin 6 :=
  (Fintype.equivFin _).trans (finCongr (by fin_cases v <;> decide))
private def D : (i : Fin 1) → Unit →* Matrix (Fin (d i)) (Fin (d i)) ℂ := fun _ => 1

-- A reversed edge and multiplicity 3, distinct from block dimension 2.
example : Nonempty (regionParentGroundSpace
    (numberedGraphOrientedAveragingTensor (blockMatrixRepresentation d D) 1
      (fun _ => true) eX) (fun _ : Unit => Finset.univ) ≃ₗ[ℂ]
    regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 (fun _ => true) eM)
      (fun _ : Unit => Finset.univ)) :=
  ⟨canonicalOrientedPositiveMultiplicityParentEquiv d m (fun _ => true) D
    (fun _ => by change 0 < 3; decide) eX eM _
    (fun _ => ⟨(), Finset.mem_univ _, Finset.mem_univ _⟩)⟩

-- The actual source top/left incoming and right/down outgoing convention.
example {w h : ℕ} [NeZero w] [NeZero h] [Fact (2 < w)] [Fact (2 < h)]
    {G X : Type*} [Group G] [Fintype X] [DecidableEq X] {p : ℕ}
    {U : G →* Matrix X X ℂ} {a : X → X → X → X → Fin p → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a)) (v : TorusVertex w h) :
    IsGInjective (graphOrientedNumberedIncidentRepresentation U torusNativeEdgeFlip v)
      (localTensorMap (groupBondTensor (torusNativeIncidentSite a)) v) :=
  ha.isGInjective_torusNativeIncidentTensor v

/--
info: 'TNLean.PEPS.nonempty_ker_regionParentHamiltonian_orientedSemiRegularGInjective_equiv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.PEPS.nonempty_ker_regionParentHamiltonian_orientedSemiRegularGInjective_equiv
/--
info: 'TNLean.PEPS.IsGInjective.isGInjective_torusNativeIncidentTensor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.PEPS.IsGInjective.isGInjective_torusNativeIncidentTensor
