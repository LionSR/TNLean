/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionProjectorCoordinates
import TNLean.PEPS.RegularChargePair

/-!
# A correlated charge-pair insertion in an actual regular block

The diagonal two-bond operator has weight χ(p η₁⁻¹ η₀). This is a correlated
weight, not a product of two independent bond characters. Compatibility with
the actual local averages determines each internal label as x⁻¹ times its tree
reference. The common translation cancels from the relative coordinate.
Source: SCP10, arXiv:1001.3807, charge-pair creation, lines 2505–2558.
These auxiliary finite-region identities make no original-spin creation or
parent-Hamiltonian assertion.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The literal two-bond correlated diagonal insertion in the original canonical
open-region contraction. Source: SCP10, charge-pair equation, lines 2505–2558. -/
def regularProjectorChargePairOpenRegionMatrix (R : Finset V)
    (e₀ e₁ : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) (χ : G → ℂ) (p : G) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R)
      ({e : Edge Γ // IsRegionBoundaryEdge R e} → G) ℂ :=
  fun α θ => ∑ η : {e : Edge Γ // IsRegionIncidentEdge R e} → G,
    if (fun f : {e : Edge Γ // IsRegionBoundaryEdge R e} =>
        η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ then
      χ (p * (η ⟨e₁.1, Or.inl e₁.2.1⟩)⁻¹ * η ⟨e₀.1, Or.inl e₀.2.1⟩) *
      ∏ w : {w : V // w ∈ R},
        regularLegProjector (IncidentEdge Γ w.1) (α w)
          (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)
    else 0

private theorem reference_weight_of_nonzero_product (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (η : {e : Edge Γ // IsRegionIncidentEdge R e} → G)
    (hne : (∏ w : {w : V // w ∈ R},
      regularLegProjector (IncidentEdge Γ w.1)
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c w)
        (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)) ≠ 0) :
    ∃ x : G, ∀ e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R},
      c.2.1 e = x * η ⟨e.1, Or.inl e.2.1⟩ := by
  classical
  have hex (w : {w : V // w ∈ R}) : ∃ q : G,
      (regularRegionCoordinatesEquiv R T hT htree o).symm c w =
        q • (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩) := by
    have hp : regularLegProjector (IncidentEdge Γ w.1)
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c w)
        (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩) ≠ 0 := by
      intro hz
      exact hne (Finset.prod_eq_zero (Finset.mem_univ w) hz)
    rw [regularLegProjector_apply] at hp
    have hs : (∑ g : G, if
        (regularRegionCoordinatesEquiv R T hT htree o).symm c w =
          g • (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)
        then (1 : ℂ) else 0) ≠ 0 := fun hz => hp (by rw [hz, mul_zero])
    obtain ⟨q, _, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    refine ⟨q, ?_⟩
    by_contra hq'
    exact hq (by rw [ite_eq_right hq'])
  choose q hq using hex
  have ht (e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) :
      c.2.2.1.1 ⟨e.1.1.1,e.2.1⟩ * c.2.1 e =
        q ⟨e.1.1.1,e.2.1⟩ * η ⟨e.1, Or.inl e.2.1⟩ := by
    have h := congrFun (hq ⟨e.1.1.1,e.2.1⟩)
      (⟨e.1, Or.inl rfl⟩ : IncidentEdge Γ e.1.1.1)
    rw [regularRegionCoordinatesEquiv_symm_internal_tail R T hT htree o c e] at h
    exact h
  have hα (e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R})
      (he : T.Adj ⟨e.1.1.1,e.2.1⟩ ⟨e.1.1.2,e.2.2⟩) :
      c.2.2.1.1 ⟨e.1.1.1,e.2.1⟩ * c.2.1 e =
        q ⟨e.1.1.1,e.2.1⟩ * η ⟨e.1, Or.inl e.2.1⟩ ∧
      c.2.2.1.1 ⟨e.1.1.2,e.2.2⟩ * c.2.1 e =
        q ⟨e.1.1.2,e.2.2⟩ * η ⟨e.1, Or.inl e.2.1⟩ := by
    refine ⟨ht e, ?_⟩
    have h := congrFun (hq ⟨e.1.1.2,e.2.2⟩)
      (⟨e.1, Or.inr rfl⟩ : IncidentEdge Γ e.1.1.2)
    rw [regularRegionCoordinatesEquiv_symm_internal_head R T hT htree o c e] at h
    simpa only [he, dite_eq_left trivial, mul_one, Pi.smul_apply, smul_eq_mul] using h
  have hroot := regularRegionCoordinates_rootLabels_of_tree_compatibility
    R T hT htree o c η q hα
  refine ⟨q o, fun e => ?_⟩
  have h := ht e
  rw [hroot, mul_assoc] at h
  exact mul_left_cancel h

/-- The actual correlated two-bond insertion depends only on the two internal
reference labels. The unknown tree translation cancels from their relative
coordinate. Source: SCP10, charge creation, lines 2505–2558. -/
theorem regularProjectorChargePairOpenRegionMatrix_coordinates (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (e₀ e₁ : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) (χ : G → ℂ) (p : G)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorChargePairOpenRegionMatrix R e₀ e₁ χ p
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
      χ (p * (c.2.1 e₁)⁻¹ * c.2.1 e₀) *
        regularProjectorOpenRegionMatrix R
          ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ := by
  classical
  rw [regularProjectorChargePairOpenRegionMatrix, regularProjectorOpenRegionMatrix,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  split_ifs
  · by_cases hz : (∏ w : {w : V // w ∈ R},
        regularLegProjector (IncidentEdge Γ w.1)
          ((regularRegionCoordinatesEquiv R T hT htree o).symm c w)
          (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)) = 0
    · rw [hz, mul_zero, mul_zero]
    · obtain ⟨x, hx⟩ := reference_weight_of_nonzero_product R T hT htree o c η hz
      rw [hx e₀, hx e₁]
      congr 2
      group
  · exact (mul_zero _).symm

end TNLean.PEPS
