/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionCommutingConstraints

/-!
# Overlapping regional constraints in regular coordinates

All constraints act on the half-edges of one ambient graph. Vertex averages,
shared-edge averages and regional flat-support projectors commute, including
when their regions overlap. This is the virtual commutation step for SCP10,
Theorem 6.12. The physical range identification is not an assumption here.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Restrict global half-edge coordinates to a region, retaining all its
boundary half-edges. -/
def restrictRegularRegionHalfEdges (R : Finset V)
    (α : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ) :
    RegionHalfEdgeConfig (Γ := Γ) G R :=
  fun v => α ⟨v.1, Finset.mem_univ _⟩

/-- Regional flatness imposed diagonally on the full ambient half-edge space. -/
noncomputable def regularGlobalRegionFlatProjector (R : Finset V) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ)
      (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ) ℂ := by
  classical
  exact Matrix.diagonal (fun α =>
    if IsRegularRegionHalfEdgeFlat R (restrictRegularRegionHalfEdges R α) then 1 else 0)

/-- A flatness condition on any region commutes with every shared right-edge
translation on the ambient graph. -/
theorem regularGlobalRegionFlatProjector_commute_right (R : Finset V) (r : Edge Γ → G) :
    Commute (regularGlobalRegionFlatProjector (G := G) R)
      (Matrix.permMatrixHom (R := ℂ) (regularRegionHalfEdgeRightEquiv Finset.univ r)) := by
  classical
  let E := regularRegionHalfEdgeRightEquiv Finset.univ r
  change Commute _ (Equiv.Perm.permMatrix ℂ E.symm)
  apply Matrix.commute_permMatrix_of_entry_invariant
  intro α β
  have hrestrict : restrictRegularRegionHalfEdges R (E.symm α) =
      regularRegionHalfEdgeRightMul R (fun e => (r e)⁻¹)
        (restrictRegularRegionHalfEdges R α) := rfl
  simp only [regularGlobalRegionFlatProjector, Matrix.diagonal_apply, E.symm.injective.eq_iff]
  rw [hrestrict, isRegularRegionHalfEdgeFlat_rightMul_iff]

/-- A regional flatness condition commutes with every independent ambient
left vertex translation. -/
theorem regularGlobalRegionFlatProjector_commute_vertexTranslation (R : Finset V)
    (k : {v : V // v ∈ (Finset.univ : Finset V)} → G) :
    Commute (regularGlobalRegionFlatProjector (Γ := Γ) (G := G) R)
      (regularRegionVertexTranslationMatrix Finset.univ k) := by
  classical
  let E := regularRegionGaugePhysicalLabels (Γ := Γ) Finset.univ (fun v => (k v)⁻¹)
  change Commute _ (Equiv.Perm.permMatrix ℂ E.symm)
  apply Matrix.commute_permMatrix_of_entry_invariant
  intro α β
  have hrestrict : restrictRegularRegionHalfEdges R (E.symm α) =
      regularRegionGaugePhysicalLabels R (fun v => k ⟨v.1, Finset.mem_univ _⟩)
        (restrictRegularRegionHalfEdges R α) := by
    funext v e
    change ((k ⟨v.1, Finset.mem_univ _⟩)⁻¹)⁻¹⁻¹ * _ = _
    rw [inv_inv]
    rfl
  simp only [regularGlobalRegionFlatProjector, Matrix.diagonal_apply, E.symm.injective.eq_iff]
  rw [hrestrict, isRegularRegionHalfEdgeFlat_gauge_iff]

/-- Regional flatness constraints commute without any restriction on overlap. -/
theorem regularGlobalRegionFlatProjector_commute (R S : Finset V) :
    Commute (regularGlobalRegionFlatProjector (Γ := Γ) (G := G) R)
      (regularGlobalRegionFlatProjector (Γ := Γ) (G := G) S) := by
  classical
  unfold regularGlobalRegionFlatProjector
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext α
  exact mul_comm _ _

/-- A vertex average in the ambient regular half-edge space. -/
noncomputable def regularGlobalVertexAverage (v : V) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ)
      (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
    regularRegionVertexTranslationMatrix Finset.univ (fun w => if w.1 = v then g else 1)

/-- Any regional flatness condition commutes with every ambient vertex average. -/
theorem regularGlobalRegionFlatProjector_commute_vertexAverage (R : Finset V) (v : V) :
    Commute (regularGlobalRegionFlatProjector (Γ := Γ) (G := G) R)
      (regularGlobalVertexAverage (Γ := Γ) (G := G) v) := by
  unfold regularGlobalVertexAverage
  apply Commute.smul_right
  exact Commute.sum_right Finset.univ _ _ (fun g _ =>
    regularGlobalRegionFlatProjector_commute_vertexTranslation R _)

/-- Any regional flatness condition commutes with every ambient edge average. -/
theorem regularGlobalRegionFlatProjector_commute_edgeAverage (R : Finset V) (e : Edge Γ) :
    Commute (regularGlobalRegionFlatProjector (Γ := Γ) (G := G) R)
      (regularRegionEdgeAverage (G := G) Finset.univ e) := by
  unfold regularRegionEdgeAverage
  apply Commute.smul_right
  exact Commute.sum_right Finset.univ _ _ (fun g _ =>
    regularGlobalRegionFlatProjector_commute_right R _)

/-- Vertex and edge averages commute on the ambient graph. -/
theorem regularGlobalVertexAverage_commute_edgeAverage (v : V) (e : Edge Γ) :
    Commute (regularGlobalVertexAverage (Γ := Γ) (G := G) v)
      (regularRegionEdgeAverage (G := G) Finset.univ e) := by
  unfold regularGlobalVertexAverage
  apply Commute.smul_left
  exact Commute.sum_left Finset.univ _ _ (fun g _ =>
    (regularRegionEdgeAverage_commute_vertexTranslation Finset.univ e _).symm)

/-- Vertex averages commute, whether or not their vertices coincide. -/
theorem regularGlobalVertexAverage_commute (v w : V) :
    Commute (regularGlobalVertexAverage (Γ := Γ) (G := G) v)
      (regularGlobalVertexAverage (Γ := Γ) (G := G) w) := by
  by_cases hvw : v = w
  · subst w
    exact Commute.refl _
  unfold regularGlobalVertexAverage
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sum_left
  intro g _
  apply Commute.sum_right
  intro h _
  unfold regularRegionVertexTranslationMatrix
  apply Commute.map _ (Matrix.permMatrixHom (R := ℂ))
  apply Equiv.ext
  intro α
  funext a e
  simp only [Equiv.Perm.mul_apply, regularRegionGaugePhysicalLabels_apply, inv_inv]
  split_ifs <;> simp_all

/-- The three kinds of constraints in the ambient half-edge coordinates:
vertex averages, edge averages, and regional flatness projectors. -/
noncomputable def regularGlobalConstraint (i : V ⊕ Edge Γ ⊕ Finset V) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ)
      (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ) ℂ :=
  match i with
  | Sum.inl v => regularGlobalVertexAverage v
  | Sum.inr (Sum.inl e) => regularRegionEdgeAverage Finset.univ e
  | Sum.inr (Sum.inr R) => regularGlobalRegionFlatProjector R

/-- All three families of constraints commute on the original ambient graph. -/
theorem regularGlobalConstraint_commute (i j : V ⊕ Edge Γ ⊕ Finset V) :
    Commute (regularGlobalConstraint (G := G) i) (regularGlobalConstraint (G := G) j) := by
  rcases i with v | e | R <;> rcases j with w | f | S
  · exact regularGlobalVertexAverage_commute v w
  · exact regularGlobalVertexAverage_commute_edgeAverage v f
  · exact (regularGlobalRegionFlatProjector_commute_vertexAverage S v).symm
  · exact (regularGlobalVertexAverage_commute_edgeAverage w e).symm
  · exact regularRegionEdgeAverage_commute Finset.univ e f
  · exact (regularGlobalRegionFlatProjector_commute_edgeAverage S e).symm
  · exact regularGlobalRegionFlatProjector_commute_vertexAverage R w
  · exact regularGlobalRegionFlatProjector_commute_edgeAverage R f
  · exact regularGlobalRegionFlatProjector_commute R S

/-- Products of these concrete constraints commute in any order. -/
theorem regularGlobalConstraint_list_prod_commute
    (l m : List (V ⊕ Edge Γ ⊕ Finset V)) :
    Commute (l.map (regularGlobalConstraint (G := G))).prod
      (m.map (regularGlobalConstraint (G := G))).prod := by
  apply Commute.list_prod_left
  intro a ha
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
  apply Commute.list_prod_right
  intro b hb
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hb
  exact regularGlobalConstraint_commute i j

/-- The virtual constraint for a region: average its vertices and internal
edges, then restrict to configurations with trivial internal holonomy.
No condition is imposed on the unused physical directions of a site tensor. -/
noncomputable def regularGlobalRegionConstraint (R : Finset V) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ)
      (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ) ℂ :=
  ((R.toList.map Sum.inl ++
    ((Finset.univ.filter (fun e : Edge Γ => e.1.1 ∈ R ∧ e.1.2 ∈ R)).toList.map
      (fun e => Sum.inr (Sum.inl e))) ++ [Sum.inr (Sum.inr R)]).map
        (regularGlobalConstraint (G := G))).prod

/-- Concrete virtual regional constraints commute for arbitrary overlapping
regions of a finite graph. This is the virtual part of SCP10, Theorem 6.12;
it does not assume commutation of physical parent interactions. -/
theorem regularGlobalRegionConstraint_commute (R S : Finset V) :
    Commute (regularGlobalRegionConstraint (Γ := Γ) (G := G) R)
      (regularGlobalRegionConstraint (Γ := Γ) (G := G) S) :=
  regularGlobalConstraint_list_prod_commute _ _

end TNLean.PEPS
