/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularOverlappingConstraints
import TNLean.Algebra.FiniteGroupUnitaryAverage

/-!
# Orthogonal projectors for the regular regional constraints

The commuting virtual constraints are orthogonal projections. Their product
is therefore the orthogonal projection onto their common fixed space.
Source: SCP10, arXiv:1001.3807, Theorem 6.12, lines 2131–2153.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Left multiplication at a single ambient vertex is a group representation. -/
def regularGlobalVertexPermutation (v : V) :
    G →* Equiv.Perm (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ) where
  toFun g := regularRegionGaugePhysicalLabels Finset.univ
    (fun w => (if w.1 = v then g else 1)⁻¹)
  map_one' := by
    ext α w e
    simp only [regularRegionGaugePhysicalLabels_apply, ite_self, inv_one, one_mul,
      Equiv.Perm.one_apply]
  map_mul' g h := by
    ext α w e
    simp only [Equiv.Perm.mul_apply, regularRegionGaugePhysicalLabels_apply, inv_inv]
    split_ifs <;> simp only [one_mul, mul_assoc]

/-- The ambient vertex average is an orthogonal projector. -/
theorem regularGlobalVertexAverage_isStarProjection (v : V) :
    IsStarProjection (regularGlobalVertexAverage (Γ := Γ) (G := G) v) := by
  classical
  let ρ : G →* Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ) ℂ :=
    { toFun := fun g => ⟨Matrix.permMatrixHom (R := ℂ)
        (regularGlobalVertexPermutation (Γ := Γ) v g),
        Equiv.Perm.permMatrix_mem_unitaryGroup _⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro g h; apply Subtype.ext; simp }
  exact TNLean.Algebra.isStarProjection_inv_card_smul_sum ρ

/-- Every ambient regional flatness matrix is an orthogonal projector. -/
theorem regularGlobalRegionFlatProjector_isStarProjection (R : Finset V) :
    IsStarProjection (regularGlobalRegionFlatProjector (Γ := Γ) (G := G) R) := by
  classical
  apply (isStarProjection_iff').mpr
  constructor
  · rw [regularGlobalRegionFlatProjector, Matrix.diagonal_mul_diagonal]
    congr 1
    funext α
    split_ifs <;> simp
  · change (regularGlobalRegionFlatProjector R)ᴴ = regularGlobalRegionFlatProjector R
    ext α β
    simp only [regularGlobalRegionFlatProjector, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all

/-- Every member of the three concrete constraint families is an orthogonal projector. -/
theorem regularGlobalConstraint_isStarProjection (i : V ⊕ Edge Γ ⊕ Finset V) :
    IsStarProjection (regularGlobalConstraint (G := G) i) := by
  rcases i with v | e | R
  · exact regularGlobalVertexAverage_isStarProjection v
  · exact regularRegionEdgeAverage_isStarProjection Finset.univ e
  · exact regularGlobalRegionFlatProjector_isStarProjection R

/-- A finite product of the concrete commuting constraints is an orthogonal projector. -/
theorem regularGlobalConstraint_list_prod_isStarProjection
    (l : List (V ⊕ Edge Γ ⊕ Finset V)) :
    IsStarProjection (l.map (regularGlobalConstraint (G := G))).prod := by
  induction l with
  | nil => exact IsStarProjection.one _
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    apply (regularGlobalConstraint_isStarProjection i).mul ih
    apply Commute.list_prod_right
    intro a ha
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
    exact regularGlobalConstraint_commute i j

/-- The concrete virtual regional constraint is an orthogonal projector. -/
theorem regularGlobalRegionConstraint_isStarProjection (R : Finset V) :
    IsStarProjection (regularGlobalRegionConstraint (Γ := Γ) (G := G) R) :=
  regularGlobalConstraint_list_prod_isStarProjection _

private theorem mulVec_mul_eq_self_iff {ι : Type*} [Fintype ι]
    {P Q : Matrix ι ι ℂ} (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : Commute P Q)
    (x : ι → ℂ) : (P * Q) *ᵥ x = x ↔ P *ᵥ x = x ∧ Q *ᵥ x = x := by
  constructor
  · intro h
    constructor
    · have hh := congrArg (fun y => P *ᵥ y) h
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hP, h] at hh
      exact hh.symm
    · have hh := congrArg (fun y => Q *ᵥ y) h
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPQ.symm.eq,
        Matrix.mul_assoc, hQ, h] at hh
      exact hh.symm
  · rintro ⟨hP, hQ⟩
    rw [← Matrix.mulVec_mulVec, hQ, hP]

/-- The product fixes precisely the vectors fixed by every listed constraint. -/
theorem regularGlobalConstraint_list_prod_mulVec_eq_self_iff
    (l : List (V ⊕ Edge Γ ⊕ Finset V))
    (x : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) :
    (l.map (regularGlobalConstraint (G := G))).prod *ᵥ x = x ↔
      ∀ i ∈ l, regularGlobalConstraint (G := G) i *ᵥ x = x := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    have hc : Commute (regularGlobalConstraint (G := G) i)
        (l.map (regularGlobalConstraint (G := G))).prod := by
      apply Commute.list_prod_right
      intro a ha
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
      exact regularGlobalConstraint_commute i j
    rw [mulVec_mul_eq_self_iff
      (regularGlobalConstraint_isStarProjection i).isIdempotentElem.eq
      (regularGlobalConstraint_list_prod_isStarProjection l).isIdempotentElem.eq hc, ih]
    simp

/-- The virtual regional projector fixes exactly the vectors obeying its
vertex, internal-edge and flat-support constraints. -/
theorem regularGlobalRegionConstraint_mulVec_eq_self_iff (R : Finset V)
    (x : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) :
    regularGlobalRegionConstraint (Γ := Γ) (G := G) R *ᵥ x = x ↔
      (∀ v ∈ R, regularGlobalVertexAverage (Γ := Γ) (G := G) v *ᵥ x = x) ∧
      (∀ e : Edge Γ, e.1.1 ∈ R → e.1.2 ∈ R →
        regularRegionEdgeAverage (G := G) Finset.univ e *ᵥ x = x) ∧
      regularGlobalRegionFlatProjector (Γ := Γ) (G := G) R *ᵥ x = x := by
  classical
  rw [regularGlobalRegionConstraint, regularGlobalConstraint_list_prod_mulVec_eq_self_iff]
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
    true_and, regularGlobalConstraint, and_assoc, and_imp]
  simp

end TNLean.PEPS
