/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionBondRightInvariance
import TNLean.PEPS.RegularCycleControlledSupport
import TNLean.Algebra.PermutationMatrixCommutation

/-!
# Commuting constraints in regular half-edge coordinates

Left multiplication at a vertex and shared right multiplication on an edge
commute, without assuming that the group is abelian. The internal flatness
condition is preserved by both operations. These are the virtual constraints
in the two-dimensional proof of SCP10, Theorem 6.12.

This file establishes the virtual commutation identities. Identifying their
joint projector with the physical regional parent projector is a separate step.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Reversible shared right multiplication on the half-edges in a region.
The multiplier is indexed by the original edges, so its values agree at the
two endpoints of every internal edge. -/
def regularRegionHalfEdgeRightEquiv (R : Finset V) (r : Edge Γ → G) :
    Equiv.Perm (RegionHalfEdgeConfig (Γ := Γ) G R) :=
  Equiv.piCongrRight fun _ => Equiv.piCongrRight fun e => Equiv.mulRight (r e.1)

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
@[simp]
theorem regularRegionHalfEdgeRightEquiv_apply (R : Finset V) (r : Edge Γ → G)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
    regularRegionHalfEdgeRightEquiv R r α = regularRegionHalfEdgeRightMul R r α := rfl

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Left vertex multiplication commutes with shared right edge multiplication.
This uses associativity and does not require an abelian group. -/
theorem regularRegionHalfEdgeRightEquiv_commute_gauge (R : Finset V)
    (r : Edge Γ → G) (k : {v : V // v ∈ R} → G) :
    Commute (regularRegionHalfEdgeRightEquiv R r) (regularRegionGaugePhysicalLabels R k) := by
  apply Equiv.ext
  intro α
  funext v e
  exact mul_assoc _ _ _

/-- The same left-right identity for the actual permutation matrices. -/
theorem regularRegionHalfEdgeRightMatrix_commute_vertexTranslation (R : Finset V)
    (r : Edge Γ → G) (k : {v : V // v ∈ R} → G) :
    Commute (Matrix.permMatrixHom (R := ℂ) (regularRegionHalfEdgeRightEquiv R r))
      (regularRegionVertexTranslationMatrix R k) :=
  (regularRegionHalfEdgeRightEquiv_commute_gauge R r (fun v => (k v)⁻¹)).map
    (Matrix.permMatrixHom (R := ℂ))

/-- Shared right translations preserve the product of the actual local
regular invariant projectors. -/
theorem regularRegionHalfEdgeRightMatrix_commute_localProjector (R : Finset V)
    (r : Edge Γ → G) :
    Commute (Matrix.permMatrixHom (R := ℂ) (regularRegionHalfEdgeRightEquiv R r))
      (regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))) := by
  apply commute_regionLocalProjector_of_vertexTranslation
  exact regularRegionHalfEdgeRightMatrix_commute_vertexTranslation R r

/-- A regional configuration is flat when independent vertex gauges can make
the two half-edge labels of every internal edge equal. -/
def IsRegularRegionHalfEdgeFlat (R : Finset V)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) : Prop :=
  ∃ k : {v : V // v ∈ R} → G,
    ∀ e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R},
      (k ⟨e.1.1.1, e.2.1⟩)⁻¹ * α ⟨e.1.1.1, e.2.1⟩ ⟨e.1, Or.inl rfl⟩ =
      (k ⟨e.1.1.2, e.2.2⟩)⁻¹ * α ⟨e.1.1.2, e.2.2⟩ ⟨e.1, Or.inr rfl⟩

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Shared right edge multiplication preserves regional flatness. -/
theorem isRegularRegionHalfEdgeFlat_rightMul_iff (R : Finset V) (r : Edge Γ → G)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
    IsRegularRegionHalfEdgeFlat R (regularRegionHalfEdgeRightMul R r α) ↔
      IsRegularRegionHalfEdgeFlat R α := by
  simp only [IsRegularRegionHalfEdgeFlat, regularRegionHalfEdgeRightMul,
    ← mul_assoc, mul_right_cancel_iff]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Independent vertex gauges preserve regional flatness. -/
theorem isRegularRegionHalfEdgeFlat_gauge_iff (R : Finset V)
    (q : {v : V // v ∈ R} → G) (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
    IsRegularRegionHalfEdgeFlat R (regularRegionGaugePhysicalLabels R q α) ↔
      IsRegularRegionHalfEdgeFlat R α := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨fun v => q v * k v, ?_⟩
    intro e
    simpa only [regularRegionGaugePhysicalLabels_apply, mul_inv_rev, mul_assoc] using hk e
  · rintro ⟨k, hk⟩
    refine ⟨fun v => (q v)⁻¹ * k v, ?_⟩
    intro e
    simpa only [regularRegionGaugePhysicalLabels_apply, mul_inv_rev, inv_inv,
      mul_assoc, mul_inv_cancel_left] using hk e

/-- The diagonal projector onto the flat regional configurations. -/
noncomputable def regularRegionFlatProjector (R : Finset V) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ := by
  classical
  exact Matrix.diagonal (fun α => if IsRegularRegionHalfEdgeFlat R α then 1 else 0)

/-- The flat-support projector commutes with every shared right translation,
including those on boundary edges. -/
theorem regularRegionFlatProjector_commute_right (R : Finset V) (r : Edge Γ → G) :
    Commute (regularRegionFlatProjector (Γ := Γ) (G := G) R)
      (Matrix.permMatrixHom (R := ℂ) (regularRegionHalfEdgeRightEquiv R r)) := by
  classical
  change Commute _ (Equiv.Perm.permMatrix ℂ (regularRegionHalfEdgeRightEquiv R r).symm)
  apply Matrix.commute_permMatrix_of_entry_invariant
  intro α β
  have he : (regularRegionHalfEdgeRightEquiv R r).symm =
      regularRegionHalfEdgeRightEquiv R (fun e => (r e)⁻¹) := by
    ext α v e
    rfl
  rw [he]
  simp only [regularRegionFlatProjector, Matrix.diagonal_apply]
  simp only [(regularRegionHalfEdgeRightEquiv R (fun e => (r e)⁻¹)).injective.eq_iff]
  simp only [regularRegionHalfEdgeRightEquiv_apply, isRegularRegionHalfEdgeFlat_rightMul_iff]

/-- The flat-support projector commutes with independent left vertex translations. -/
theorem regularRegionFlatProjector_commute_vertexTranslation (R : Finset V)
    (k : {v : V // v ∈ R} → G) :
    Commute (regularRegionFlatProjector (Γ := Γ) (G := G) R)
      (regularRegionVertexTranslationMatrix R k) := by
  classical
  change Commute _ (Equiv.Perm.permMatrix ℂ
    (regularRegionGaugePhysicalLabels R (fun v => (k v)⁻¹)).symm)
  apply Matrix.commute_permMatrix_of_entry_invariant
  intro α β
  have he : (regularRegionGaugePhysicalLabels (Γ := Γ) R (fun v => (k v)⁻¹)).symm =
      regularRegionGaugePhysicalLabels R k := by
    ext α v e
    change ((k v)⁻¹)⁻¹⁻¹ * α v e = (k v)⁻¹ * α v e
    rw [inv_inv]
  rw [he]
  simp only [regularRegionFlatProjector, Matrix.diagonal_apply,
    (regularRegionGaugePhysicalLabels (Γ := Γ) R k).injective.eq_iff,
    isRegularRegionHalfEdgeFlat_gauge_iff]

/-- The flat-support projector commutes with the product of local regular projectors. -/
theorem regularRegionFlatProjector_commute_localProjector (R : Finset V) :
    Commute (regularRegionFlatProjector (Γ := Γ) (G := G) R)
      (regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))) := by
  apply commute_regionLocalProjector_of_vertexTranslation
  exact regularRegionFlatProjector_commute_vertexTranslation R

/-- The right-translation average on one original edge, acting on its incident
half-edges in the region. -/
noncomputable def regularRegionEdgeAverage (R : Finset V) (e : Edge Γ) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
    Matrix.permMatrixHom (R := ℂ)
      (regularRegionHalfEdgeRightEquiv R (fun f => if f = e then g else 1))

/-- A right-edge average commutes with the flat-support projector. -/
theorem regularRegionEdgeAverage_commute_flatProjector (R : Finset V) (e : Edge Γ) :
    Commute (regularRegionEdgeAverage (G := G) R e)
      (regularRegionFlatProjector (Γ := Γ) (G := G) R) := by
  apply Commute.symm
  unfold regularRegionEdgeAverage
  apply Commute.smul_right
  exact Commute.sum_right Finset.univ _ _ (fun g _ =>
    regularRegionFlatProjector_commute_right R _)

/-- A right-edge average commutes with every independent left vertex translation. -/
theorem regularRegionEdgeAverage_commute_vertexTranslation (R : Finset V) (e : Edge Γ)
    (k : {v : V // v ∈ R} → G) :
    Commute (regularRegionEdgeAverage (G := G) R e)
      (regularRegionVertexTranslationMatrix R k) := by
  unfold regularRegionEdgeAverage
  apply Commute.smul_left
  exact Commute.sum_left Finset.univ _ _ (fun g _ =>
    regularRegionHalfEdgeRightMatrix_commute_vertexTranslation R _ k)

/-- A right-edge average commutes with the product of left vertex averages. -/
theorem regularRegionEdgeAverage_commute_localProjector (R : Finset V) (e : Edge Γ) :
    Commute (regularRegionEdgeAverage (G := G) R e)
      (regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))) := by
  unfold regularRegionEdgeAverage
  apply Commute.smul_left
  exact Commute.sum_left Finset.univ _ _ (fun g _ =>
    regularRegionHalfEdgeRightMatrix_commute_localProjector R _)

/-- Right-edge averages commute, even for a nonabelian group. Distinct edges
act on different half-edge coordinates; coincident edges give the same average. -/
theorem regularRegionEdgeAverage_commute (R : Finset V) (e f : Edge Γ) :
    Commute (regularRegionEdgeAverage (G := G) R e)
      (regularRegionEdgeAverage (G := G) R f) := by
  by_cases hef : e = f
  · subst f
    exact Commute.refl _
  unfold regularRegionEdgeAverage
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sum_left
  intro g _
  apply Commute.sum_right
  intro h _
  apply Commute.map _ (Matrix.permMatrixHom (R := ℂ))
  apply Equiv.ext
  intro α
  funext v a
  change (α v a * (if a.1 = f then h else 1)) * (if a.1 = e then g else 1) =
    (α v a * (if a.1 = e then g else 1)) * (if a.1 = f then h else 1)
  split_ifs <;> simp_all

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem edgeRight_mul (R : Finset V) (e : Edge Γ) (g h : G) :
    regularRegionHalfEdgeRightEquiv R (fun f => if f = e then g else 1) *
        regularRegionHalfEdgeRightEquiv R (fun f => if f = e then h else 1) =
      regularRegionHalfEdgeRightEquiv R (fun f => if f = e then h * g else 1) := by
  ext α v f
  change (α v f * (if f.1 = e then h else 1)) * (if f.1 = e then g else 1) =
    α v f * (if f.1 = e then h * g else 1)
  split_ifs <;> simp only [mul_one, mul_assoc]

/-- Averaging twice over one edge is the same as averaging once. -/
theorem regularRegionEdgeAverage_mul_self (R : Finset V) (e : Edge Γ) :
    regularRegionEdgeAverage (G := G) R e * regularRegionEdgeAverage R e =
      regularRegionEdgeAverage R e := by
  classical
  let M (g : G) := Matrix.permMatrixHom (R := ℂ)
    (regularRegionHalfEdgeRightEquiv R (fun f => if f = e then g else 1))
  have hM (g h : G) : M g * M h = M (h * g) := by
    dsimp only [M]
    rw [← map_mul, edgeRight_mul]
  have hsum (g : G) : (∑ h : G, M (h * g)) = ∑ h : G, M h :=
    Equiv.sum_comp (Equiv.mulRight g) M
  change ((Fintype.card G : ℂ)⁻¹ • ∑ g, M g) *
      ((Fintype.card G : ℂ)⁻¹ • ∑ g, M g) =
    (Fintype.card G : ℂ)⁻¹ • ∑ g, M g
  rw [smul_mul_smul_comm, Finset.sum_mul]
  simp_rw [Finset.mul_sum, hM, hsum]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  congr 1
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- The average over a shared right-edge action is self-adjoint. -/
theorem regularRegionEdgeAverage_isHermitian (R : Finset V) (e : Edge Γ) :
    (regularRegionEdgeAverage (G := G) R e).IsHermitian := by
  classical
  let E (g : G) := regularRegionHalfEdgeRightEquiv R (fun f => if f = e then g else 1)
  have hinv (g : G) : (E g)⁻¹ = E g⁻¹ := by
    ext α v f
    change α v f * (if f.1 = e then g else 1)⁻¹ =
      α v f * (if f.1 = e then g⁻¹ else 1)
    split_ifs <;> simp
  let M (g : G) := Matrix.permMatrixHom (R := ℂ) (E g)
  have hstar (g : G) : (M g)ᴴ = M g⁻¹ := by
    change (Equiv.Perm.permMatrix ℂ (E g)⁻¹)ᴴ =
      Equiv.Perm.permMatrix ℂ (E g⁻¹)⁻¹
    rw [Matrix.conjTranspose_permMatrix, inv_inv, hinv, inv_inv]
  change ((Fintype.card G : ℂ)⁻¹ • ∑ g, M g)ᴴ =
    (Fintype.card G : ℂ)⁻¹ • ∑ g, M g
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [hstar]
  have hsum := Equiv.sum_comp (Equiv.inv G) M
  simp only [Equiv.inv_apply] at hsum
  rw [hsum]
  congr 1
  simp

/-- The right-edge average is an orthogonal projector. -/
theorem regularRegionEdgeAverage_isStarProjection (R : Finset V) (e : Edge Γ) :
    IsStarProjection (regularRegionEdgeAverage (G := G) R e) :=
  (isStarProjection_iff').mpr ⟨regularRegionEdgeAverage_mul_self R e,
    regularRegionEdgeAverage_isHermitian R e⟩

/-- The flat-support matrix is an orthogonal projector. -/
theorem regularRegionFlatProjector_isStarProjection (R : Finset V) :
    IsStarProjection (regularRegionFlatProjector (Γ := Γ) (G := G) R) := by
  classical
  apply (isStarProjection_iff').mpr
  constructor
  · rw [regularRegionFlatProjector, Matrix.diagonal_mul_diagonal]
    congr 1
    funext α
    split_ifs <;> simp
  · change (regularRegionFlatProjector R)ᴴ = regularRegionFlatProjector R
    ext α β
    simp only [regularRegionFlatProjector, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all

end TNLean.PEPS
