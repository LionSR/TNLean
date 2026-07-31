/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingFormSpatialBridge

/-!
# Neighboring operators from a translation-invariant commuting bond

This file extracts the positive neighboring operators in the spatial decomposition of a
single translation-invariant commuting bond.  The same one-site unitary is used at both
ends of the bond, so the resulting family is independent of the position of the bond in a
finite chain.

## Main declarations

* `Matrix.etaPairSpatialBlockEquiv`
* `Matrix.exists_positive_etaPair_decomposition_of_overlappingLifts_commute`
* `MPOTensor.TranslationInvariantBondData.exists_positive_eta_pairBond_decomposition`
* `MPOTensor.EtaLocalStructureData.exists_positive_eta_pairBond_decomposition`

## References

* S. Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1.
* arXiv:1606.00608, Appendix C.2, equation sigmaNK2, lines 1581--1605.
-/

open scoped ComplexOrder Kronecker Matrix

namespace Matrix

variable {d : ℕ}

/-- The index equivalence which orders a pair of spatially decomposed sites as
\[
  H_{q,l}\otimes(H_{q,r}\otimes H_{h,l})\otimes H_{h,r}.
\]

This is the order in which a neighboring operator acts between sectors \(q\) and \(h\) in
arXiv:1606.00608, Appendix C.2, equation sigmaNK2, lines 1581--1589. -/
def etaPairSpatialBlockEquiv {K : ℕ} {dl dr : Fin K → ℕ}
    (e : ((q : Fin K) × (Fin (dr q) × Fin (dl q))) ≃ Fin d) :
    ((qh : Fin K × Fin K) ×
      ((Fin (dl qh.1) × (Fin (dr qh.1) × Fin (dl qh.2))) × Fin (dr qh.2))) ≃
      (Fin d × Fin d) where
  toFun x :=
    (e ⟨x.1.1, (x.2.1.2.1, x.2.1.1)⟩,
      e ⟨x.1.2, (x.2.2, x.2.1.2.2)⟩)
  invFun y :=
    let x := e.symm y.1
    let z := e.symm y.2
    ⟨(x.1, z.1), ((x.2.2, (x.2.1, z.2.2)), z.2.1)⟩
  left_inv x := by
    obtain ⟨⟨q, h⟩, ⟨⟨lq, rq, lh⟩, rh⟩⟩ := x
    simp only
    rw [e.symm_apply_apply, e.symm_apply_apply]
  right_inv y := by
    obtain ⟨i, j⟩ := y
    simp only
    rw [e.apply_symm_apply, e.apply_symm_apply]

/-- A positive two-site operator whose overlapping translates commute has one spatial
decomposition and a positive neighboring operator \(\eta_{q,h}\) for each ordered pair of
sectors such that
\[
  (U^*\otimes U^*)B(U\otimes U)
    =\bigoplus_{q,h}\mathbf 1_{q,l}\otimes\eta_{q,h}\otimes\mathbf 1_{h,r}.
\]

This is the local matrix argument transporting Beigi's one-sided block actions to the
symmetric two-sided coordinates used in equation sigmaNK2.  It assumes only positivity of
the two-site operator and commutation of its two overlapping lifts.

No zero-correlation-length or area-law hypothesis is used.  In particular, this theorem
does not assert the rank-one trace factorization invoked later in Proposition 4to2.

Source: arXiv:1606.00608, Appendix C.2, equation sigmaNK2 and Proposition 4to2,
lines 1581--1605; Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III,
equation (2). -/
theorem exists_positive_etaPair_decomposition_of_overlappingLifts_commute
    (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hB : B.PosSemidef)
    (hComm : Matrix.leftOverlappingLift B * Matrix.rightOverlappingLift B =
      Matrix.rightOverlappingLift B * Matrix.leftOverlappingLift B) :
    ∃ (K : ℕ) (dl dr : Fin K → ℕ)
      (e : ((q : Fin K) × (Fin (dr q) × Fin (dl q))) ≃ Fin d)
      (U : Matrix (Fin d) (Fin d) ℂ)
      (η : (q h : Fin K) →
        Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
        (∀ q, 0 < dl q) ∧ (∀ q, 0 < dr q) ∧
        (∀ q h, (η q h).PosSemidef) ∧
        Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
            (Matrix.etaPairSpatialBlockEquiv e).symm
            (star (U ⊗ₖ U) * B * (U ⊗ₖ U)) =
          Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
            ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
              η qh.1 qh.2) ⊗ₖ
                (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ) := by
  classical
  obtain ⟨K, dl, dr, e, U, R, S, hU, hdl, hdr, _, _, hR, hS⟩ :=
    Matrix.exists_unitary_blockActions_of_overlappingLifts_commute B B
      hB.isHermitian hB.isHermitian hComm
  let B' := star (U ⊗ₖ U) * B * (U ⊗ₖ U)
  let BR := star ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ U) * B *
    ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ U)
  let BS := star (U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * B *
    (U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))
  let η : (q h : Fin K) →
      Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ :=
    fun q h x y ↦
      B' (e ⟨q, (x.1, ⟨0, hdl q⟩)⟩, e ⟨h, (⟨0, hdr h⟩, x.2)⟩)
        (e ⟨q, (y.1, ⟨0, hdl q⟩)⟩, e ⟨h, (⟨0, hdr h⟩, y.2)⟩)
  have hUU_left : U ⊗ₖ U =
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ U) *
        (U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    rw [← Matrix.mul_kronecker_mul]
    simp
  have hUU_right : U ⊗ₖ U =
      (U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ U) := by
    rw [← Matrix.mul_kronecker_mul]
    simp
  have hB'_left : B' =
      star (U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * BR *
        (U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    dsimp only [B', BR]
    rw [hUU_left, star_mul]
    noncomm_ring
  have hB'_right : B' =
      star ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ U) * BS *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ U) := by
    dsimp only [B', BS]
    rw [hUU_right, star_mul]
    noncomm_ring
  have hR_entry (i i' : Fin d) (h : Fin K) (lh lh' : Fin (dl h))
      (rh rh' : Fin (dr h)) :
      BR (i, e ⟨h, (rh, lh)⟩) (i', e ⟨h, (rh', lh')⟩) =
        R h (i, lh) (i', lh') *
          (1 : Matrix (Fin (dr h)) (Fin (dr h)) ℂ) rh rh' := by
    have hEntry := congrFun (congrFun hR ⟨h, ((i, lh), rh)⟩)
      ⟨h, ((i', lh'), rh')⟩
    simpa [BR, Matrix.reindex_apply, Matrix.leftSpatialBlockEquiv,
      Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply] using hEntry
  have hR_entry_ne (i i' : Fin d) (h h' : Fin K) (hh : h ≠ h')
      (lh : Fin (dl h)) (lh' : Fin (dl h')) (rh : Fin (dr h)) (rh' : Fin (dr h')) :
      BR (i, e ⟨h, (rh, lh)⟩) (i', e ⟨h', (rh', lh')⟩) = 0 := by
    have hEntry := congrFun (congrFun hR ⟨h, ((i, lh), rh)⟩)
      ⟨h', ((i', lh'), rh')⟩
    simpa [BR, Matrix.reindex_apply, Matrix.leftSpatialBlockEquiv,
      Matrix.blockDiagonal'_apply_ne _ _ _ hh] using hEntry
  have hS_entry (q : Fin K) (lq lq' : Fin (dl q)) (rq rq' : Fin (dr q))
      (j j' : Fin d) :
      BS (e ⟨q, (rq, lq)⟩, j) (e ⟨q, (rq', lq')⟩, j') =
        (1 : Matrix (Fin (dl q)) (Fin (dl q)) ℂ) lq lq' *
          S q (rq, j) (rq', j') := by
    have hEntry := congrFun (congrFun hS ⟨q, (lq, (rq, j))⟩)
      ⟨q, (lq', (rq', j'))⟩
    simpa [BS, Matrix.reindex_apply, Matrix.rightSpatialBlockEquiv,
      Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply] using hEntry
  have hS_entry_ne (q q' : Fin K) (hq : q ≠ q')
      (lq : Fin (dl q)) (lq' : Fin (dl q')) (rq : Fin (dr q)) (rq' : Fin (dr q'))
      (j j' : Fin d) :
      BS (e ⟨q, (rq, lq)⟩, j) (e ⟨q', (rq', lq')⟩, j') = 0 := by
    have hEntry := congrFun (congrFun hS ⟨q, (lq, (rq, j))⟩)
      ⟨q', (lq', (rq', j'))⟩
    simpa [BS, Matrix.reindex_apply, Matrix.rightSpatialBlockEquiv,
      Matrix.blockDiagonal'_apply_ne _ _ _ hq] using hEntry
  have hB'_right_sector_ne (q q' h h' : Fin K) (hh : h ≠ h')
      (lq : Fin (dl q)) (lq' : Fin (dl q'))
      (rq : Fin (dr q)) (rq' : Fin (dr q'))
      (lh : Fin (dl h)) (lh' : Fin (dl h'))
      (rh : Fin (dr h)) (rh' : Fin (dr h')) :
      B' (e ⟨q, (rq, lq)⟩, e ⟨h, (rh, lh)⟩)
          (e ⟨q', (rq', lq')⟩, e ⟨h', (rh', lh')⟩) = 0 := by
    rw [hB'_left]
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, Fintype.sum_prod_type]
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [hR_entry_ne _ _ h h' hh]
    simp only [mul_zero, zero_mul, Finset.sum_const_zero]
  have hB'_left_sector_ne (q q' h h' : Fin K) (hq : q ≠ q')
      (lq : Fin (dl q)) (lq' : Fin (dl q'))
      (rq : Fin (dr q)) (rq' : Fin (dr q'))
      (lh : Fin (dl h)) (lh' : Fin (dl h'))
      (rh : Fin (dr h)) (rh' : Fin (dr h')) :
      B' (e ⟨q, (rq, lq)⟩, e ⟨h, (rh, lh)⟩)
          (e ⟨q', (rq', lq')⟩, e ⟨h', (rh', lh')⟩) = 0 := by
    rw [hB'_right]
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, Fintype.sum_prod_type]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul]
    simp [hS_entry_ne q q' hq]
  have hB'_from_R (q q' h : Fin K)
      (lq : Fin (dl q)) (lq' : Fin (dl q'))
      (rq : Fin (dr q)) (rq' : Fin (dr q'))
      (lh lh' : Fin (dl h)) (rh rh' : Fin (dr h)) :
      B' (e ⟨q, (rq, lq)⟩, e ⟨h, (rh, lh)⟩)
          (e ⟨q', (rq', lq')⟩, e ⟨h, (rh', lh')⟩) =
        (1 : Matrix (Fin (dr h)) (Fin (dr h)) ℂ) rh rh' *
          ∑ i', (∑ i, star U (e ⟨q, (rq, lq)⟩) i *
            R h (i, lh) (i', lh')) * U i' (e ⟨q', (rq', lq')⟩) := by
    rw [hB'_left]
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, Fintype.sum_prod_type]
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [hR_entry]
    simp [Matrix.one_apply]
  have hB'_from_S (q h h' : Fin K)
      (lq lq' : Fin (dl q)) (rq rq' : Fin (dr q))
      (lh : Fin (dl h)) (lh' : Fin (dl h'))
      (rh : Fin (dr h)) (rh' : Fin (dr h')) :
      B' (e ⟨q, (rq, lq)⟩, e ⟨h, (rh, lh)⟩)
          (e ⟨q, (rq', lq')⟩, e ⟨h', (rh', lh')⟩) =
        (1 : Matrix (Fin (dl q)) (Fin (dl q)) ℂ) lq lq' *
          ∑ j', (∑ j, star U (e ⟨h, (rh, lh)⟩) j *
            S q (rq, j) (rq', j')) * U j' (e ⟨h', (rh', lh')⟩) := by
    rw [hB'_right]
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, Fintype.sum_prod_type]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul]
    simp [hS_entry, Matrix.one_apply]
  have hB'_same_sector (q h : Fin K)
      (lq lq' : Fin (dl q)) (rq rq' : Fin (dr q))
      (lh lh' : Fin (dl h)) (rh rh' : Fin (dr h)) :
      B' (e ⟨q, (rq, lq)⟩, e ⟨h, (rh, lh)⟩)
          (e ⟨q, (rq', lq')⟩, e ⟨h, (rh', lh')⟩) =
        (1 : Matrix (Fin (dl q)) (Fin (dl q)) ℂ) lq lq' *
          η q h (rq, lh) (rq', lh') *
            (1 : Matrix (Fin (dr h)) (Fin (dr h)) ℂ) rh rh' := by
    by_cases hl : lq = lq'
    · subst lq'
      by_cases hr : rh = rh'
      · subst rh'
        let l0 : Fin (dl q) := ⟨0, hdl q⟩
        let r0 : Fin (dr h) := ⟨0, hdr h⟩
        have hleft := hB'_from_S q h h lq lq rq rq' lh lh' rh rh
        have hleft0 := hB'_from_S q h h l0 l0 rq rq' lh lh' rh rh
        have hright := hB'_from_R q q h l0 l0 rq rq' lh lh' rh rh
        have hright0 := hB'_from_R q q h l0 l0 rq rq' lh lh' r0 r0
        simp only [Matrix.one_apply_eq, one_mul] at hleft hleft0 hright hright0
        rw [hleft, ← hleft0, hright, ← hright0]
        simp [η, l0, r0]
      · rw [hB'_from_R]
        simp [hr]
    · rw [hB'_from_S]
      simp [Matrix.one_apply, hl]
  refine ⟨K, dl, dr, e, U, η, hU, hdl, hdr, ?_, ?_⟩
  · intro q h
    have hBpos : B'.PosSemidef := by
      have hconj := hB.mul_mul_conjTranspose_same (B := star (U ⊗ₖ U))
      simpa [B', Matrix.star_eq_conjTranspose] using hconj
    let f : Fin (dr q) × Fin (dl h) → Fin d × Fin d := fun x ↦
      (e ⟨q, (x.1, ⟨0, hdl q⟩)⟩, e ⟨h, (⟨0, hdr h⟩, x.2)⟩)
    have hsub := hBpos.submatrix f
    change (B'.submatrix f f).PosSemidef
    exact hsub
  · change Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
        (Matrix.etaPairSpatialBlockEquiv e).symm B' = _
    ext ⟨⟨q, h⟩, ⟨⟨lq, ⟨rq, lh⟩⟩, rh⟩⟩
      ⟨⟨q', h'⟩, ⟨⟨lq', ⟨rq', lh'⟩⟩, rh'⟩⟩
    change B' (e ⟨q, (rq, lq)⟩, e ⟨h, (rh, lh)⟩)
        (e ⟨q', (rq', lq')⟩, e ⟨h', (rh', lh')⟩) = _
    by_cases hq : q = q'
    · subst q'
      by_cases hh : h = h'
      · subst h'
        rw [Matrix.blockDiagonal'_apply_eq]
        simpa [Matrix.kroneckerMap_apply] using
          hB'_same_sector q h lq lq' rq rq' lh lh' rh rh'
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun hp ↦ hh (Prod.mk.inj hp).2)]
        exact hB'_right_sector_ne q q h h' hh lq lq' rq rq' lh lh' rh rh'
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun hp ↦ hq (Prod.mk.inj hp).1)]
      exact hB'_left_sector_ne q q' h h' hq lq lq' rq rq' lh lh' rh rh'

end Matrix

namespace MPOTensor.TranslationInvariantBondData

variable {d : ℕ}

/-- A positive translation-invariant commuting bond has one chain-independent symmetric
eta-pair decomposition.

Source: arXiv:1606.00608, Appendix C.2, equation sigmaNK2 and Proposition 4to2,
lines 1581--1605; Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1. -/
theorem exists_positive_eta_pairBond_decomposition
    (data : TranslationInvariantBondData d) :
    ∃ (K : ℕ) (dl dr : Fin K → ℕ)
      (e : ((q : Fin K) × (Fin (dr q) × Fin (dl q))) ≃ Fin d)
      (U : Matrix (Fin d) (Fin d) ℂ)
      (η : (q h : Fin K) →
        Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
        (∀ q, 0 < dl q) ∧ (∀ q, 0 < dr q) ∧
        (∀ q h, (η q h).PosSemidef) ∧
        Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
            (Matrix.etaPairSpatialBlockEquiv e).symm
            (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)) =
          Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
            ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
              η qh.1 qh.2) ⊗ₖ
                (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ) := by
  have hpair : data.pairBond.PosSemidef := by
    have hsub := data.bond_pos.submatrix (finTwoArrowEquiv (Fin d)).symm
    simpa [TranslationInvariantBondData.pairBond, pairBondMatrix,
      Matrix.reindex_apply] using hsub
  exact Matrix.exists_positive_etaPair_decomposition_of_overlappingLifts_commute
    data.pairBond hpair data.overlappingLifts_pairBond_comm

end MPOTensor.TranslationInvariantBondData

namespace MPOTensor.EtaLocalStructureData

variable {d D : ℕ} {M : MPOTensor d D}

/-- A positive bond carried by an eta-local structure has one chain-independent unitary
sector decomposition with positive neighboring operators.

Source: arXiv:1606.00608, Appendix C.2, equation sigmaNK2 and Proposition 4to2,
lines 1581--1605; Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1. -/
theorem exists_positive_eta_pairBond_decomposition
    (data : EtaLocalStructureData M) :
    ∃ (K : ℕ) (dl dr : Fin K → ℕ)
      (e : ((q : Fin K) × (Fin (dr q) × Fin (dl q))) ≃ Fin d)
      (U : Matrix (Fin d) (Fin d) ℂ)
      (η : (q h : Fin K) →
        Matrix (Fin (dr q) × Fin (dl h)) (Fin (dr q) × Fin (dl h)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
        (∀ q, 0 < dl q) ∧ (∀ q, 0 < dr q) ∧
        (∀ q h, (η q h).PosSemidef) ∧
        Matrix.reindex (Matrix.etaPairSpatialBlockEquiv e).symm
            (Matrix.etaPairSpatialBlockEquiv e).symm
            (star (U ⊗ₖ U) * data.pairBond * (U ⊗ₖ U)) =
          Matrix.blockDiagonal' fun qh : Fin K × Fin K ↦
            ((1 : Matrix (Fin (dl qh.1)) (Fin (dl qh.1)) ℂ) ⊗ₖ
              η qh.1 qh.2) ⊗ₖ
                (1 : Matrix (Fin (dr qh.2)) (Fin (dr qh.2)) ℂ) := by
  exact data.bondData.exists_positive_eta_pairBond_decomposition

end MPOTensor.EtaLocalStructureData
