/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularProjectorChargePairCoordinates
import TNLean.PEPS.RegularChargeReferencePreparation
import TNLean.PEPS.RegularCycleControlledSupport
import QICLean.Algebra.MatrixReindexUnitary
import TNLean.PEPS.RegularPhysicalChargeMotion

/-!
# Charge-pair preparation in the actual internal references of a regular block

The two reference labels are isolated by a genuine coordinate equivalence.
A simultaneous-left-invariant unitary acts there, and every other physical
coordinate is retained. Source: SCP10, arXiv:1001.3807, lines 2505–2558.

**Scope restriction (finite-region reference coordinates):** The preparation
and return-projection identities are stated in the reference coordinates of a
supplied finite block with a chosen tree and two internal bonds. They do not
identify a prescribed six-site region, a decomposition of the physical state,
or a completed geometric braid (lines 2560–2615). See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
private abbrev Internal (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev Vertex (R : Finset V) := {v : V // v ∈ R}
variable (R : Finset V) (T : SimpleGraph (Vertex R)) [DecidableRel T.Adj]
private abbrev OtherReferences (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁) :=
  {f : {e : Internal (Γ := Γ) R // e ≠ e₀} // f ≠ ⟨e₁, hne.symm⟩} → G
private def referencePairSplit (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁) :
    (Internal (Γ := Γ) R → G) ≃ (G × G) × OtherReferences (G := G) R e₀ e₁ hne :=
  (Equiv.funSplitAt e₀ G).trans
    (((Equiv.refl G).prodCongr (Equiv.funSplitAt ⟨e₁, hne.symm⟩ G)).trans
      (Equiv.prodAssoc G G _).symm)
private abbrev Rest (o : Vertex R) (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁) :=
  ({f : Edge Γ // IsRegionBoundaryEdge R f} → G) ×
    OtherReferences (G := G) R e₀ e₁ hne ×
    RootedGroupLabels (G := G) o × (RegionCycleEdge (Γ := Γ) R T → G)
private def referenceSplit (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁) :
    RegularRegionCoordinates (Γ := Γ) (G := G) R T o ≃
      (G × G) × Rest (G := G) R T o e₀ e₁ hne where
  toFun c := ((referencePairSplit R e₀ e₁ hne c.2.1).1,
    c.1, (referencePairSplit R e₀ e₁ hne c.2.1).2, c.2.2.1, c.2.2.2)
  invFun c := (c.2.1, (referencePairSplit R e₀ e₁ hne).symm (c.1,c.2.2.1),
    c.2.2.2.1,c.2.2.2.2)
  left_inv c := by
    change (c.1, (referencePairSplit R e₀ e₁ hne).symm
      (referencePairSplit R e₀ e₁ hne c.2.1), c.2.2.1,c.2.2.2) = c
    rw [Equiv.symm_apply_apply]
  right_inv c := by
    rcases c with ⟨a,y,b,r,z⟩
    change (((referencePairSplit R e₀ e₁ hne)
      ((referencePairSplit R e₀ e₁ hne).symm (a,b))).1, y,
      ((referencePairSplit R e₀ e₁ hne)
        ((referencePairSplit R e₀ e₁ hne).symm (a,b))).2, r, z) = (a,y,b,r,z)
    rw [Equiv.apply_symm_apply]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G]
  [DecidableRel T.Adj] in
private theorem referenceSplit_translation_rest (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁) (ℓ : Vertex R → G)
    (c d : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    (referenceSplit R T o e₀ e₁ hne (regularRegionCoordinateTranslation R T o ℓ c)).2 =
      (referenceSplit R T o e₀ e₁ hne (regularRegionCoordinateTranslation R T o ℓ d)).2 ↔
    (referenceSplit R T o e₀ e₁ hne c).2 = (referenceSplit R T o e₀ e₁ hne d).2 := by
  simp only [referenceSplit, referencePairSplit, Equiv.coe_fn_mk,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.prodAssoc_symm_apply, Equiv.funSplitAt_apply, regularRegionCoordinateTranslation,
    Prod.mk.injEq, Subtype.ext_iff, funext_iff, mul_left_cancel_iff, mul_right_cancel_iff]

private theorem matrix_pair_entries_of_commute (Q : Matrix (G × G) (G × G) ℂ) (x : G)
    (hQ : Commute Q (leftRegularMatrix G x ⊗ₖ leftRegularMatrix G x))
    (r s a b : G) : Q (x*r,x*s) (x*a,x*b) = Q (r,s) (a,b) := by
  have h := congrArg (fun M : Matrix (G × G) (G × G) ℂ => M (x*r,x*s) (a,b)) hQ.eq
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    leftRegularMatrix_apply, mul_left_cancel_iff, mul_ite, ite_mul,
    one_mul, zero_mul, mul_one, mul_zero] at h
  simpa using h

private def coordinatePreparation (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (Q : Matrix (G × G) (G × G) ℂ) :
    Matrix (RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
      (RegularRegionCoordinates (Γ := Γ) (G := G) R T o) ℂ := by
  classical
  exact (Q.kronecker (1 : Matrix (Rest (G := G) R T o e₀ e₁ hne) _ ℂ)).submatrix
    (referenceSplit R T o e₀ e₁ hne) (referenceSplit R T o e₀ e₁ hne)

omit [DecidableRel T.Adj] in
private theorem coordinatePreparation_translation (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (Q : Matrix (G × G) (G × G) ℂ)
    (hQ : ∀ x, Commute Q (leftRegularMatrix G x ⊗ₖ leftRegularMatrix G x))
    (ℓ : Vertex R → G) (c d : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    coordinatePreparation R T o e₀ e₁ hne Q (regularRegionCoordinateTranslation R T o ℓ c)
        (regularRegionCoordinateTranslation R T o ℓ d) =
      coordinatePreparation R T o e₀ e₁ hne Q c d := by
  classical
  simp only [coordinatePreparation, Matrix.submatrix_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [referenceSplit_translation_rest R T o e₀ e₁ hne ℓ c d]
  congr 1
  change Q (ℓ o * c.2.1 e₀, ℓ o * c.2.1 e₁)
    (ℓ o * d.2.1 e₀, ℓ o * d.2.1 e₁) = Q (c.2.1 e₀,c.2.1 e₁) (d.2.1 e₀,d.2.1 e₁)
  exact matrix_pair_entries_of_commute Q (ℓ o) (hQ (ℓ o)) _ _ _ _

/-- Act on two actual internal reference labels and retain every other physical
coordinate. Source: SCP10, charge-pair accessible operation, lines 2534–2558. -/
def regularRegionChargeReferenceMatrix
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (Q : Matrix (G × G) (G × G) ℂ) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
  (coordinatePreparation R T o e₀ e₁ hne Q).submatrix
    (regularRegionCoordinatesEquiv R T hT htree o)
    (regularRegionCoordinatesEquiv R T hT htree o)

/-- The actual reference-coordinate extension preserves unitarity.
Source: SCP10, charge-pair accessible operation, lines 2534–2558. -/
theorem regularRegionChargeReferenceMatrix_mem_unitaryGroup
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (Q : Matrix (G × G) (G × G) ℂ) (hQ : Q ∈ Matrix.unitaryGroup _ ℂ) :
    regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q ∈
      Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ := by
  classical
  let := Fintype.ofFinite (RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
  let := Fintype.ofFinite (Rest (G := G) R T o e₀ e₁ hne)
  let C := RegularRegionCoordinates (Γ := Γ) (G := G) R T o
  let B := Rest (G := G) R T o e₀ e₁ hne
  let S := referenceSplit (G := G) R T o e₀ e₁ hne
  have hprod : Q.kronecker (1 : Matrix B B ℂ) ∈
      Matrix.unitaryGroup ((G × G) × B) ℂ :=
    Matrix.kronecker_mem_unitary hQ (Matrix.unitaryGroup B ℂ).one_mem
  have hcoord : coordinatePreparation R T o e₀ e₁ hne Q ∈
      Matrix.unitaryGroup C ℂ := by
    exact Matrix.reindex_mem_unitaryGroup (m := (G × G) × B) (n := C) S.symm
      (Q.kronecker (1 : Matrix B B ℂ)) hprod
  exact Matrix.reindex_mem_unitaryGroup (m := C)
    (n := RegionHalfEdgeConfig (Γ := Γ) G R)
    (regularRegionCoordinatesEquiv R T hT htree o).symm
    (coordinatePreparation R T o e₀ e₁ hne Q) hcoord

/-- Simultaneous-left symmetry of the reference operation implies commutation
with every actual independent vertex translation. Source: SCP10, lines 2520–2558. -/
theorem regularRegionChargeReferenceMatrix_commute_vertexTranslation
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (Q : Matrix (G × G) (G × G) ℂ)
    (hQ : ∀ x, Commute Q (leftRegularMatrix G x ⊗ₖ leftRegularMatrix G x))
    (ℓ : Vertex R → G) :
    Commute (regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q)
      (regularRegionVertexTranslationMatrix (Γ := Γ) R ℓ) := by
  classical
  let E := regularRegionCoordinatesEquiv (G := G) R T hT htree o
  let τ : Equiv.Perm (RegionHalfEdgeConfig (Γ := Γ) G R) :=
    regularRegionGaugePhysicalLabels (Γ := Γ) R (fun v => (ℓ v)⁻¹)
  have hE (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
      E (τ α) = regularRegionCoordinateTranslation R T o ℓ (E α) := by
    apply E.symm.injective
    rw [E.symm_apply_apply, regularRegionCoordinatesEquiv_symm_coordinateTranslation,
      E.symm_apply_apply]
  have hi (α β : RegionHalfEdgeConfig (Γ := Γ) G R) :
      regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q (τ α) (τ β) =
        regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q α β := by
    change coordinatePreparation R T o e₀ e₁ hne Q (E (τ α)) (E (τ β)) =
      coordinatePreparation R T o e₀ e₁ hne Q (E α) (E β)
    rw [hE, hE, coordinatePreparation_translation R T o e₀ e₁ hne Q hQ]
  change Commute _ ((τ⁻¹).permMatrix ℂ)
  apply Matrix.commute_permMatrix_of_entry_invariant
  intro α β
  simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using
    (hi (τ.symm α) (τ.symm β)).symm

/-- The actual reference preparation commutes with the product local regular
averaging projector. Source: SCP10, charge-pair creation, lines 2534–2558. -/
theorem regularRegionChargeReferenceMatrix_commute_localProjector
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (Q : Matrix (G × G) (G × G) ℂ)
    (hQ : ∀ x, Commute Q (leftRegularMatrix G x ⊗ₖ leftRegularMatrix G x)) :
    Commute (regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q)
      (regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))) :=
  commute_regionLocalProjector_of_vertexTranslation R _ (fun ℓ =>
    regularRegionChargeReferenceMatrix_commute_vertexTranslation R T
      hT htree o e₀ e₁ hne Q hQ ℓ)

/-- The reference operation acts on the actual canonical boundary columns, producing
precisely the correlated two-bond charge insertion. No column or Gram identity is
assumed. Source: SCP10, charge-pair creation, lines 2534–2558. -/
theorem regularRegionChargeReferenceMatrix_mulVec
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (Q : Matrix (G × G) (G × G) ℂ) (χ : G → ℂ) (p : G)
    (hact : Q *ᵥ (fun _ : G × G => (1 : ℂ)) = regularChargePairCoefficient χ p)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q *ᵥ
        (fun α => regularProjectorOpenRegionMatrix R α θ) =
      fun α => regularProjectorChargePairOpenRegionMatrix R e₀ e₁ χ p α θ := by
  classical
  let := Fintype.ofFinite (RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
  let := Fintype.ofFinite (Rest (G := G) R T o e₀ e₁ hne)
  let E := regularRegionCoordinatesEquiv (G := G) R T hT htree o
  let S := referenceSplit (G := G) R T o e₀ e₁ hne
  let F (b : Rest (G := G) R T o e₀ e₁ hne) : ℂ :=
    (Fintype.card G : ℂ) * (Fintype.card G : ℂ)⁻¹ ^ R.card *
      regularLegProjector {e : Edge Γ // IsRegionBoundaryEdge R e} b.1 θ *
      (if b.2.2.2 = 1 then 1 else 0)
  have hcol (s : G × G) (b : Rest (G := G) R T o e₀ e₁ hne) :
      regularProjectorOpenRegionMatrix R (E.symm (S.symm (s,b))) θ = F b := by
    rw [regularProjectorOpenRegionMatrix_coordinates R T hT htree o]
    rfl
  funext α
  have htarget : regularProjectorChargePairOpenRegionMatrix R e₀ e₁ χ p α θ =
      regularChargePairCoefficient χ p (S (E α)).1 * F (S (E α)).2 := by
    have h := regularProjectorChargePairOpenRegionMatrix_coordinates
      R T hT htree o e₀ e₁ χ p (E α) θ
    rw [E.symm_apply_apply] at h
    rw [h]
    rw [show regularProjectorOpenRegionMatrix R α θ = F (S (E α)).2 from by
      simpa only [S.symm_apply_apply, E.symm_apply_apply] using
        hcol (S (E α)).1 (S (E α)).2]
    rfl
  have hentry (s : G × G) (b : Rest (G := G) R T o e₀ e₁ hne) :
      regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q α
          (E.symm (S.symm (s,b))) =
        Q (S (E α)).1 s * (if (S (E α)).2 = b then 1 else 0) := by
    change (Q.kronecker (1 : Matrix _ _ ℂ)) (S (E α)) (S (E (E.symm (S.symm (s,b))))) = _
    rw [E.apply_symm_apply, S.apply_symm_apply]
    rfl
  rw [htarget, Matrix.mulVec, dotProduct, ← E.symm.sum_comp, ← S.symm.sum_comp,
    Fintype.sum_prod_type]
  simp_rw [hentry, hcol]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_mul]
  have h := congrFun hact (S (E α)).1
  simpa only [Matrix.mulVec, dotProduct, mul_one] using
    congrArg (fun t : ℂ => t * F (S (E α)).2) h

/-- Extending a reference operation respects the adjoint.
Source: SCP10, accessible-register return measurement, lines 2582–2615. -/
theorem regularRegionChargeReferenceMatrix_conjTranspose
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (Q : Matrix (G × G) (G × G) ℂ) :
    (regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q).conjTranspose =
      regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q.conjTranspose := by
  classical
  simp only [regularRegionChargeReferenceMatrix, coordinatePreparation,
    Matrix.conjTranspose_submatrix, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

/-- Extending a reference operation respects composition.
Source: SCP10, accessible-register return measurement, lines 2582–2615. -/
theorem regularRegionChargeReferenceMatrix_mul
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (Q U : Matrix (G × G) (G × G) ℂ) :
    regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne (Q * U) =
      regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q *
        regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne U := by
  classical
  let := Fintype.ofFinite (RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
  let := Fintype.ofFinite (Rest (G := G) R T o e₀ e₁ hne)
  unfold regularRegionChargeReferenceMatrix coordinatePreparation
  simp only [Matrix.kronecker]
  rw [Matrix.submatrix_mul_equiv _ _ _
    (regularRegionCoordinatesEquiv R T hT htree o) _]
  rw [Matrix.submatrix_mul_equiv _ _ _ (referenceSplit R T o e₀ e₁ hne) _]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- A Hermitian reference operation remains Hermitian on the actual block.
Source: SCP10, accessible-register return measurement, lines 2582–2615. -/
theorem regularRegionChargeReferenceMatrix_isHermitian
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (Q : Matrix (G × G) (G × G) ℂ) (hQ : Q.IsHermitian) :
    (regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q).IsHermitian := by
  change _ = _
  rw [regularRegionChargeReferenceMatrix_conjTranspose, hQ.eq]

/-- An idempotent reference operation remains idempotent on the actual block.
Source: SCP10, accessible-register return measurement, lines 2582–2615. -/
theorem regularRegionChargeReferenceMatrix_mul_self
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁)
    (Q : Matrix (G × G) (G × G) ℂ) (hQ : Q * Q = Q) :
    regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q *
        regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q =
      regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q := by
  rw [← regularRegionChargeReferenceMatrix_mul, hQ]

private theorem braided_column_coordinates
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (χ : G → ℂ) (p k : G)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorWeightedTwistedRegionMatrix R (fun _ => 1)
        (fun η => χ (p * (η ⟨e₁.1,Or.inl e₁.2.1⟩)⁻¹ * k⁻¹ *
          η ⟨e₀.1,Or.inl e₀.2.1⟩))
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
      (Fintype.card G : ℂ)⁻¹ ^ R.card * ∑ x : G,
        if c.1 = x • θ ∧ c.2.2.2 = 1 then
          regularBraidedChargePairCoefficient χ p k x (c.2.1 e₀,c.2.1 e₁) else 0 := by
  classical
  rw [regularProjectorWeightedTwistedRegionMatrix_coordinates,
    regularRegionTreeGauge_one]
  have hb : regularRegionBoundaryTransport R (fun _ => (1 : G)) (fun _ => 1) θ = θ := by
    funext e
    simp [regularRegionBoundaryTransport]
  simp only [hb, regularRegionTreeCycleResidual, regularRegionGaugeResidual,
    regularRegionTreeGauge_one, inv_one, mul_one, mul_inv_cancel, Pi.one_def]
  apply congrArg ((Fintype.card G : ℂ)⁻¹ ^ R.card * ·)
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · simp only [regularRegionTreeReferenceLabels, dite_eq_left e₀.2.1,
      dite_eq_left e₀.2.2, dite_eq_left e₁.2.1, dite_eq_left e₁.2.2,
      one_mul, mul_inv_rev, inv_inv, regularBraidedChargePairCoefficient,
      mul_assoc]
  · rfl

private theorem initial_weighted_column (e₀ e₁ : Internal (Γ := Γ) R)
    (χ : G → ℂ) (p : G) (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorWeightedTwistedRegionMatrix R (fun _ => 1)
        (fun η => χ (p * (η ⟨e₁.1,Or.inl e₁.2.1⟩)⁻¹ * (1 : G)⁻¹ *
          η ⟨e₀.1,Or.inl e₀.2.1⟩)) α θ =
      regularProjectorChargePairOpenRegionMatrix R e₀ e₁ χ p α θ := by
  classical
  unfold regularProjectorWeightedTwistedRegionMatrix
    regularProjectorChargePairOpenRegionMatrix
  apply Finset.sum_congr rfl
  intro η _
  split_ifs
  · have hlabels (w : Vertex R) :
        regularTwistedLabels (fun _ : Edge Γ => (1 : G)) w.1
          (fun f => η ⟨f.1,isRegionIncidentEdge_of_regionVertex R w f⟩) =
        (fun f => η ⟨f.1,isRegionIncidentEdge_of_regionVertex R w f⟩) := by
      funext f
      simp [regularTwistedLabels]
    simp_rw [hlabels]
    simp only [inv_one, mul_one]
  · rfl

/-- The return projection acts on the literal correlated weighted canonical
column. The boundary and common-root sums are derived from the original
contraction. Source: SCP10, interference calculation, lines 2582–2615. -/
theorem regularRegionChargeReferenceMatrix_mulVec_braided
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (σ : Representation ℂ G H) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹)
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (e₀ e₁ : Internal (Γ := Γ) R) (hne : e₀ ≠ e₁) (p k : G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne
        (regularChargePairReturnProjection σ.character p) *ᵥ
        (fun α => regularProjectorWeightedTwistedRegionMatrix R (fun _ => 1)
          (fun η => σ.character (p * (η ⟨e₁.1,Or.inl e₁.2.1⟩)⁻¹ * k⁻¹ *
            η ⟨e₀.1,Or.inl e₀.2.1⟩)) α θ) =
      (σ.character k⁻¹ / Module.finrank ℂ H) •
        (fun α => regularProjectorChargePairOpenRegionMatrix R e₀ e₁
          σ.character p α θ) := by
  classical
  let := Fintype.ofFinite (RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
  let := Fintype.ofFinite (Rest (G := G) R T o e₀ e₁ hne)
  let E := regularRegionCoordinatesEquiv (G := G) R T hT htree o
  let S := referenceSplit (G := G) R T o e₀ e₁ hne
  let D := regularChargePairReturnProjection σ.character p
  let n : ℂ := (Fintype.card G : ℂ)⁻¹ ^ R.card
  let B (b : Rest (G := G) R T o e₀ e₁ hne) (x : G) : Prop :=
    b.1 = x • θ ∧ b.2.2.2 = 1
  let col (l : G) (α : RegionHalfEdgeConfig (Γ := Γ) G R) : ℂ :=
    regularProjectorWeightedTwistedRegionMatrix R (fun _ => 1)
      (fun η => σ.character (p * (η ⟨e₁.1,Or.inl e₁.2.1⟩)⁻¹ * l⁻¹ *
        η ⟨e₀.1,Or.inl e₀.2.1⟩)) α θ
  have hcol (l : G) (s : G × G) (b : Rest (G := G) R T o e₀ e₁ hne) :
      col l (E.symm (S.symm (s,b))) = n * ∑ x : G,
        if B b x then regularBraidedChargePairCoefficient σ.character p l x s else 0 := by
    have hp : ((S.symm (s,b)).2.1 e₀,(S.symm (s,b)).2.1 e₁) = s :=
      congrArg Prod.fst (S.apply_symm_apply (s,b))
    dsimp only [col]
    rw [braided_column_coordinates R T hT htree o, hp]
    rfl
  have hinit (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
      col 1 α = regularProjectorChargePairOpenRegionMatrix R e₀ e₁
        σ.character p α θ := by
    exact initial_weighted_column R e₀ e₁ σ.character p α θ
  funext α
  have hentry (s : G × G) (b : Rest (G := G) R T o e₀ e₁ hne) :
      regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne D α
        (E.symm (S.symm (s,b))) =
      D (S (E α)).1 s * (if (S (E α)).2 = b then 1 else 0) := by
    change (D.kronecker (1 : Matrix _ _ ℂ)) (S (E α))
      (S (E (E.symm (S.symm (s,b))))) = _
    rw [E.apply_symm_apply, S.apply_symm_apply]
    rfl
  change (regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne D *ᵥ col k) α =
    (σ.character k⁻¹ / Module.finrank ℂ H) *
    regularProjectorChargePairOpenRegionMatrix R e₀ e₁ σ.character p α θ
  rw [← hinit, Matrix.mulVec, dotProduct, ← E.symm.sum_comp, ← S.symm.sum_comp,
    Fintype.sum_prod_type]
  simp_rw [hentry, hcol]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hα : col 1 α = n * ∑ x : G, if B (S (E α)).2 x then
      regularChargePairCoefficient σ.character p (S (E α)).1 else 0 := by
    have h := hcol 1 (S (E α)).1 (S (E α)).2
    rw [S.symm_apply_apply, E.symm_apply_apply] at h
    simpa only [regularBraidedChargePairCoefficient, inv_one,
      mul_one, mul_inv_cancel_right, regularChargePairCoefficient] using h
  rw [hα]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hb : B (S (E α)).2 x
  · simp only [hb, ite_true]
    have hm (s : G × G) : D (S (E α)).1 s *
        (n * regularBraidedChargePairCoefficient σ.character p k x s) =
      n * (D (S (E α)).1 s *
        regularBraidedChargePairCoefficient σ.character p k x s) := by ring
    simp_rw [hm]
    rw [← Finset.mul_sum]
    have h := congrFun
      (regularChargePairReturnProjection_mulVec_braidedCoefficient σ hσ p k x)
      (S (E α)).1
    change (∑ s, D (S (E α)).1 s *
      regularBraidedChargePairCoefficient σ.character p k x s) = _ at h
    rw [h]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [hb, ite_false, Finset.sum_const_zero]

end TNLean.PEPS
