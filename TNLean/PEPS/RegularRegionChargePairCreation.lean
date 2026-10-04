/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularProjectorChargePairCoordinates
import TNLean.PEPS.RegularChargeReferencePreparation
import TNLean.PEPS.RegularCycleControlledSupport
import QICLean.Algebra.MatrixReindexUnitary

/-!
# Charge-pair preparation in the actual internal references of a regular block

The two reference labels are isolated by a genuine coordinate equivalence.
A simultaneous-left-invariant unitary acts there, and every other physical
coordinate is retained. Source: SCP10, arXiv:1001.3807, lines 2505–2558.
This auxiliary block statement does not identify a prescribed six-site region.
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

end TNLean.PEPS
