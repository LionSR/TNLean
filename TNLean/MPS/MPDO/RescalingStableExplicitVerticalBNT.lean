/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Separable
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.PureAreaLaw
import TNLean.MPS.MPDO.RescalingStableChiUniformity
import TNLean.MPS.MPDO.RescalingStableLengthDependentRFPCanonicalForm
import TNLean.MPS.MPDO.VerticalSectorCoordinates

/-!
# Explicit vertical BNT clause for the rescaling-stable example

The normalized vertical component is the doubled tensor of the four matrices
`A`.  It is not the original horizontal closed MPO.

## Main definitions

* `verticalComponent` is the normalized doubled vertical component.
* `oneLabelVerticalCoisometry` is the identity coisometry for its singleton
  weighted reconstruction.
* `R_oneLabelBNTAlgebraTensorClause` packages the explicit tensor-attached
  clause with multiplicity weight `25/32` and diagonal data `oneLabelChi`.

## Main results

* `R_hasBNTAlgebraTensorClause` records the immediate existential consequence
  of the explicit one-label clause.
* `verticalComponent_isCPSVBasisOfNormalTensors` proves that the normalized
  component gives the one-label vertical BNT basis of `R`.
* `verticalBNTMPO_verticalComponent` identifies the component's rotated MPO
  tensor with `doubledTensor A`.
* `mpvOverlap_A_eq_wMat_pow_trace` identifies the component square coefficient
  with the trace powers defining `oneLabelCoeffs`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14(ii), lines 972--985, and Appendix C.4, lines 1929--1947 and
  2011--2029
-/

open scoped BigOperators ComplexOrder Matrix Kronecker

noncomputable section

namespace MPOTensor.RescalingStableLengthDependentRFP

/-- The normalized vertical component of `R`. -/
def verticalComponent : MPSTensor 16 4 :=
  (doubledTensor A).toMPSTensor

/-- The vertical tensor of `R` is `25/32` times its normalized component. -/
theorem verticalTensor_R_eq_smul_verticalComponent :
    verticalTensor R = (25 / 32 : ℂ) • verticalComponent := by
  funext ab i j
  rw [verticalTensor_apply, R_apply]
  simp only [verticalComponent, doubledTensor, MPOTensor.toMPSTensor,
    Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, bondEquiv,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.map_apply,
    starRingEnd_apply]

/-- Each letter `A a` is its nonzero value times its supporting matrix unit. -/
theorem A_eq_smul_single (a : Fin 4) :
    A a = sVal a • Matrix.single (aRow a) (aCol a) 1 := by
  fin_cases a <;> simp [A, sVal, aRow, aCol]

/-- A doubled vertical letter is a scaled matrix unit in the reindexed bond basis. -/
theorem verticalComponent_finProdFinEquiv_eq_submatrix (a b : Fin 4) :
    verticalComponent (finProdFinEquiv (a, b)) =
      (A a ⊗ₖ A b).submatrix bondEquiv.symm bondEquiv.symm := by
  unfold verticalComponent MPOTensor.toMPSTensor
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  simp only [doubledTensor, A_map_star, bondEquiv]

/-- A doubled vertical letter is a scaled matrix unit in the reindexed bond basis. -/
theorem verticalComponent_finProdFinEquiv (a b : Fin 4) :
    verticalComponent (finProdFinEquiv (a, b)) =
      (sVal a * sVal b) • Matrix.single
        (bondEquiv (aRow a, aRow b)) (bondEquiv (aCol a, aCol b)) 1 := by
  unfold verticalComponent MPOTensor.toMPSTensor
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  simp only [doubledTensor]
  rw [A_map_star, A_eq_smul_single a, A_eq_smul_single b,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
    Matrix.single_kronecker_single]
  simp only [mul_one, bondEquiv]
  change (sVal a * sVal b) •
      (Matrix.single (aRow a, aRow b) (aCol a, aCol b) 1).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm = _
  rw [Matrix.submatrix_single_equiv]
  simp only [Equiv.symm_symm]

private def aIndex : Fin 2 → Fin 2 → Fin 4
  | 0, 0 => 0
  | 1, 1 => 1
  | 0, 1 => 2
  | 1, 0 => 3

@[simp] private theorem aRow_aIndex (r c : Fin 2) : aRow (aIndex r c) = r := by
  fin_cases r <;> fin_cases c <;> rfl

@[simp] private theorem aCol_aIndex (r c : Fin 2) : aCol (aIndex r c) = c := by
  fin_cases r <;> fin_cases c <;> rfl

/-- Each matrix unit occurs as a nonzero scaled component letter. -/
theorem exists_verticalComponent_eq_smul_single (p q : Fin 4) :
    ∃ v : Fin 16, ∃ c : ℂ, c ≠ 0 ∧
      verticalComponent v = c • Matrix.single p q 1 := by
  let pp := bondEquiv.symm p
  let qq := bondEquiv.symm q
  let a := aIndex pp.1 qq.1
  let b := aIndex pp.2 qq.2
  let c : ℂ := sVal a * sVal b
  refine ⟨finProdFinEquiv (a, b), c,
    mul_ne_zero (sVal_ne_zero a) (sVal_ne_zero b), ?_⟩
  rw [verticalComponent_finProdFinEquiv]
  change c • Matrix.single
      (bondEquiv (aRow a, aRow b)) (bondEquiv (aCol a, aCol b)) 1 = _
  simp only [a, b, aRow_aIndex, aCol_aIndex]
  simp only [pp, qq, Prod.eta, Equiv.apply_symm_apply]

/-- The normalized vertical component is injective at one site. -/
theorem verticalComponent_isInjective : verticalComponent.IsInjective := by
  unfold MPSTensor.IsInjective
  apply le_antisymm le_top
  rw [← (Matrix.stdBasis ℂ (Fin 4) (Fin 4)).span_eq]
  apply Submodule.span_le.mpr
  rintro M ⟨⟨p, q⟩, rfl⟩
  rw [Matrix.stdBasis_eq_single]
  obtain ⟨v, c, hc, hv⟩ := exists_verticalComponent_eq_smul_single p q
  have hmem : verticalComponent v ∈ Submodule.span ℂ (Set.range verticalComponent) :=
    Submodule.subset_span ⟨v, rfl⟩
  rw [hv] at hmem
  have hscaled := Submodule.smul_mem (Submodule.span ℂ (Set.range verticalComponent)) c⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hscaled

/-- The four matrices `A` are left-canonical. -/
theorem A_isLeftCanonical : MPSTensor.IsLeftCanonical A := by
  unfold MPSTensor.IsLeftCanonical
  rw [Fin.sum_univ_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [A, Matrix.conjTranspose_smul, Matrix.conjTranspose_single,
      Matrix.smul_mul, Fin.isValue, ↓reduceIte, Matrix.one_apply] <;> norm_num

/-- The normalized vertical component is left-canonical. -/
theorem verticalComponent_isLeftCanonical : verticalComponent.IsLeftCanonical := by
  unfold MPSTensor.IsLeftCanonical
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16)]
  rw [Fintype.sum_prod_type]
  have hterm (a b : Fin 4) :
      (verticalComponent (finProdFinEquiv (a, b)))ᴴ *
          verticalComponent (finProdFinEquiv (a, b)) =
        (((A a)ᴴ * A a) ⊗ₖ ((A b)ᴴ * A b)).submatrix
          bondEquiv.symm bondEquiv.symm := by
    rw [verticalComponent_finProdFinEquiv_eq_submatrix,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simp_rw [hterm]
  change (∑ a : Fin 4, ∑ b : Fin 4,
      (((A a)ᴴ * A a) ⊗ₖ ((A b)ᴴ * A b))).submatrix
        bondEquiv.symm bondEquiv.symm = 1
  rw [← Matrix.sum_kronecker_sum, A_isLeftCanonical, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

/-- Algebraic injectivity makes the normalized vertical component normal. -/
theorem verticalComponent_isNormal : verticalComponent.IsNormal :=
  verticalComponent_isInjective.isNormal

/-- The normalized vertical component is a CPSV normal tensor. -/
theorem verticalComponent_isNormalTensor : verticalComponent.IsNormalTensor :=
  MPSTensor.isNormalTensor_of_isNormal_leftCanonical verticalComponent
    verticalComponent_isNormal verticalComponent_isLeftCanonical

/-- The constant physical letter used to witness a nonzero component MPV. -/
private def verticalZeroLetter : Fin 16 :=
  finProdFinEquiv ((0 : Fin 4), (0 : Fin 4))

private theorem verticalComponent_mpv_zeroLoop (N : ℕ) (hN : 0 < N) :
    MPSTensor.mpv verticalComponent (fun _ : Fin N ↦ verticalZeroLetter) =
      (16 / 25 : ℂ) ^ N := by
  rw [MPSTensor.mpv_const_eq_trace_pow]
  have hletter : verticalComponent verticalZeroLetter =
      (16 / 25 : ℂ) • Matrix.single (0 : Fin 4) (0 : Fin 4) 1 := by
    rw [verticalZeroLetter, verticalComponent_finProdFinEquiv]
    simp only [sVal, aRow, aCol]
    rw [show bondEquiv ((0 : Fin 2), (0 : Fin 2)) = (0 : Fin 4) by rfl]
    norm_num
  rw [hletter, smul_pow]
  have hE : IsIdempotentElem (Matrix.single (0 : Fin 4) (0 : Fin 4) (1 : ℂ)) := by
    simp [IsIdempotentElem, Matrix.single_mul_single_same]
  rw [hE.pow_eq (Nat.ne_of_gt hN)]
  simp [Matrix.trace, Matrix.single]

/-- The normalized vertical component is the singleton CPSV basis of normal tensors. -/
theorem verticalComponent_isCPSVBasisOfNormalTensors :
    MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor R)
      (fun _ : Fin 1 ↦ ⟨4, verticalComponent⟩) := by
  refine {
    blocks_normal := fun _ ↦ verticalComponent_isNormalTensor
    spans_mpv := ?_
    eventually_li := ?_
  }
  · intro N _hN
    refine ⟨fun _ ↦ (25 / 32 : ℂ) ^ N, ?_⟩
    intro σ
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    rw [verticalTensor_R_eq_smul_verticalComponent]
    change MPSTensor.mpv (fun i ↦ (25 / 32 : ℂ) • verticalComponent i) σ = _
    exact MPSTensor.mpv_smul (25 / 32 : ℂ) verticalComponent σ
  · refine ⟨0, ?_⟩
    intro N hN
    apply LinearIndependent.of_subsingleton (i := (0 : Fin 1))
    intro hzero
    have hcomponent := congrArg
      (fun v : MPSTensor.MPVSpace 16 N ↦ v (fun _ : Fin N ↦ verticalZeroLetter)) hzero
    have hpow : (16 / 25 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
    apply hpow
    simpa only [MPSTensor.mpvState_apply, verticalComponent_mpv_zeroLoop N hN,
      PiLp.zero_apply] using hcomponent

private abbrev oneLabelBondDim : Fin 1 → ℕ := fun _ ↦ 4
private abbrev oneLabelMultiplicity : Fin 1 → ℕ := fun _ ↦ 1
private def oneLabelWeight : (α : Fin 1) → Fin (oneLabelMultiplicity α) → ℂ :=
  fun _ _ ↦ 25 / 32
private def oneLabelVerticalFamily :
    (α : Fin 1) → MPSTensor 16 (oneLabelBondDim α) :=
  fun _ ↦ verticalComponent

private abbrev OneLabelRetainedCoordinate :=
  Fin (∑ q : Fin (∑ α : Fin 1, oneLabelMultiplicity α),
    verticalCopyDim oneLabelBondDim oneLabelMultiplicity q)

private def oneLabelSectorCoordinateEquiv :
    (Σ α : Fin 1, Fin (oneLabelMultiplicity α) ×
      Fin (oneLabelBondDim α)) ≃ Fin 4 where
  toFun x := x.2.2
  invFun i := ⟨0, (0, i)⟩
  left_inv x := by
    rcases x with ⟨α, q, i⟩
    fin_cases α
    fin_cases q
    rfl
  right_inv _ := rfl

private def oneLabelRetainedCoordinateEquiv : OneLabelRetainedCoordinate ≃ Fin 4 :=
  (verticalSectorFinEquiv oneLabelBondDim oneLabelMultiplicity).symm.trans
    oneLabelSectorCoordinateEquiv

private theorem oneLabelRetainedCoordinateEquiv_apply (x : OneLabelRetainedCoordinate) :
    oneLabelRetainedCoordinateEquiv x = x := by
  fin_cases x <;> rfl

/-- The identity coordinate matrix on the four-dimensional vertical space. -/
noncomputable def oneLabelVerticalCoisometry :
    Matrix OneLabelRetainedCoordinate (Fin 4) ℂ :=
  Matrix.reindex oneLabelRetainedCoordinateEquiv.symm (Equiv.refl (Fin 4))
    (1 : Matrix (Fin 4) (Fin 4) ℂ)

private theorem oneLabelVerticalCoisometry_apply
    (x : OneLabelRetainedCoordinate) (i : Fin 4) :
    oneLabelVerticalCoisometry x i =
      if oneLabelRetainedCoordinateEquiv x = i then 1 else 0 := by
  simp [oneLabelVerticalCoisometry, Matrix.reindex_apply, Matrix.one_apply]

private theorem oneLabel_verticalAssembledTensor :
    verticalAssembledTensor oneLabelBondDim oneLabelMultiplicity
      oneLabelWeight oneLabelVerticalFamily =
        (25 / 32 : ℂ) • verticalComponent := by
  let e : (Σ _k : Fin 1, Fin 4) ≃ Fin 4 := finSigmaFinEquiv
  have hsymm (i : Fin 4) : e.symm i = ⟨0, i⟩ := by
    apply e.injective
    rw [e.apply_symm_apply]
    ext
    exact (@finSigmaFinEquiv_one (fun _ : Fin 1 ↦ 4) ⟨(0 : Fin 1), i⟩).symm
  funext v
  ext i j
  simp only [verticalAssembledTensor, verticalCopyWeights, verticalCopyBlocks,
    verticalCopyDim, MPSTensor.toTensorFromBlocks, oneLabelWeight,
    oneLabelVerticalFamily]
  change (Matrix.reindex e e
      (Matrix.blockDiagonal' (fun _k : Fin 1 ↦
        (25 / 32 : ℂ) • verticalComponent v))) i j =
          ((25 / 32 : ℂ) • verticalComponent v) i j
  simp [Matrix.reindex_apply, hsymm]

private theorem oneLabelMultiplicity_pos (α : Fin 1) :
    0 < oneLabelMultiplicity α := by simp

private theorem oneLabelWeight_pos (α : Fin 1) (q : Fin (oneLabelMultiplicity α)) :
    (0 : ℂ) < oneLabelWeight α q := by
  norm_num [oneLabelWeight]

private theorem oneLabelVerticalCoisometry_coisometry :
    oneLabelVerticalCoisometry * oneLabelVerticalCoisometryᴴ =
      (1 : Matrix OneLabelRetainedCoordinate OneLabelRetainedCoordinate ℂ) := by
  ext x y
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    oneLabelVerticalCoisometry_apply, Matrix.one_apply]

private theorem oneLabelRetainedCoordinate_reindex_eq_self
    (X : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.reindex oneLabelRetainedCoordinateEquiv.symm
      oneLabelRetainedCoordinateEquiv.symm X = X := by
  ext x y
  simp [Matrix.reindex_apply, oneLabelRetainedCoordinateEquiv_apply]

private theorem oneLabelVerticalCoisometry_conj
    (X : Matrix (Fin 4) (Fin 4) ℂ) :
    oneLabelVerticalCoisometry * X * oneLabelVerticalCoisometryᴴ =
      Matrix.reindex oneLabelRetainedCoordinateEquiv.symm
        oneLabelRetainedCoordinateEquiv.symm X := by
  ext x y
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    oneLabelVerticalCoisometry_apply, Matrix.reindex_apply]

private theorem oneLabelVerticalCoisometry_conjTranspose :
    (oneLabelVerticalCoisometryᴴ :
      Matrix (Fin 4) OneLabelRetainedCoordinate ℂ) =
      Matrix.reindex (Equiv.refl (Fin 4))
        oneLabelRetainedCoordinateEquiv.symm
        (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i x
  rw [Matrix.conjTranspose_apply, oneLabelVerticalCoisometry_apply]
  change star (if oneLabelRetainedCoordinateEquiv x = i then 1 else 0) =
    if i = oneLabelRetainedCoordinateEquiv x then 1 else 0
  by_cases h : oneLabelRetainedCoordinateEquiv x = i
  · simp [h]
  · simp [h, Ne.symm h]

private theorem oneLabelVerticalCoisometry_reconstruction
    (X : Matrix (Fin 4) (Fin 4) ℂ) :
    oneLabelVerticalCoisometryᴴ *
      Matrix.reindex oneLabelRetainedCoordinateEquiv.symm
        oneLabelRetainedCoordinateEquiv.symm X *
      oneLabelVerticalCoisometry = X := by
  rw [oneLabelVerticalCoisometry_conjTranspose, oneLabelVerticalCoisometry]
  have hleft :
      Matrix.reindex (Equiv.refl (Fin 4)) oneLabelRetainedCoordinateEquiv.symm
          (1 : Matrix (Fin 4) (Fin 4) ℂ) *
        Matrix.reindex oneLabelRetainedCoordinateEquiv.symm
          oneLabelRetainedCoordinateEquiv.symm X =
      Matrix.reindex (Equiv.refl (Fin 4)) oneLabelRetainedCoordinateEquiv.symm
        ((1 : Matrix (Fin 4) (Fin 4) ℂ) * X) := by
    simpa only [Matrix.coe_reindexLinearEquiv] using
      Matrix.reindexLinearEquiv_mul ℂ ℂ
        (Equiv.refl (Fin 4)) oneLabelRetainedCoordinateEquiv.symm
        oneLabelRetainedCoordinateEquiv.symm
        (1 : Matrix (Fin 4) (Fin 4) ℂ) X
  rw [hleft]
  have hright :
      Matrix.reindex (Equiv.refl (Fin 4)) oneLabelRetainedCoordinateEquiv.symm
          ((1 : Matrix (Fin 4) (Fin 4) ℂ) * X) *
        Matrix.reindex oneLabelRetainedCoordinateEquiv.symm
          (Equiv.refl (Fin 4)) (1 : Matrix (Fin 4) (Fin 4) ℂ) =
      Matrix.reindex (Equiv.refl (Fin 4)) (Equiv.refl (Fin 4))
        (((1 : Matrix (Fin 4) (Fin 4) ℂ) * X) * 1) := by
    simpa only [Matrix.coe_reindexLinearEquiv] using
      Matrix.reindexLinearEquiv_mul ℂ ℂ
        (Equiv.refl (Fin 4)) oneLabelRetainedCoordinateEquiv.symm
        (Equiv.refl (Fin 4))
        ((1 : Matrix (Fin 4) (Fin 4) ℂ) * X)
        (1 : Matrix (Fin 4) (Fin 4) ℂ)
  rw [hright]
  simp [Matrix.reindex_apply]

private theorem R_vertical_forward (v : Fin 16) :
    oneLabelVerticalCoisometry * verticalTensor R v *
        oneLabelVerticalCoisometryᴴ =
      verticalAssembledTensor oneLabelBondDim oneLabelMultiplicity
        oneLabelWeight oneLabelVerticalFamily v := by
  rw [oneLabel_verticalAssembledTensor, verticalTensor_R_eq_smul_verticalComponent,
    oneLabelVerticalCoisometry_conj, oneLabelRetainedCoordinate_reindex_eq_self]

private theorem R_vertical_reconstruction (v : Fin 16) :
    verticalTensor R v = oneLabelVerticalCoisometryᴴ *
      verticalAssembledTensor oneLabelBondDim oneLabelMultiplicity
        oneLabelWeight oneLabelVerticalFamily v *
      oneLabelVerticalCoisometry := by
  rw [oneLabel_verticalAssembledTensor, verticalTensor_R_eq_smul_verticalComponent]
  have h := oneLabelVerticalCoisometry_reconstruction
    ((25 / 32 : ℂ) • verticalComponent v)
  rw [oneLabelRetainedCoordinate_reindex_eq_self] at h
  exact h.symm

/-- Separating the normalized vertical component recovers the doubled tensor. -/
theorem verticalBNTMPO_verticalComponent :
    verticalBNTMPO verticalComponent = doubledTensor A := by
  funext a b
  unfold verticalBNTMPO verticalComponent MPOTensor.toMPSTensor
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]

/-- The concrete vertical component operator is the pure-state density matrix of `A`. -/
theorem mpo_verticalBNTMPO_verticalComponent (L : ℕ) :
    mpo (verticalBNTMPO verticalComponent) L = MPSTensor.pureState A L := by
  rw [verticalBNTMPO_verticalComponent, mpo_doubledTensor]

private theorem pureState_mul_self (B : MPSTensor d D) (L : ℕ) :
    MPSTensor.pureState B L * MPSTensor.pureState B L =
      MPSTensor.mpvOverlap B B L • MPSTensor.pureState B L := by
  ext σ τ
  simp only [MPSTensor.pureState, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.smul_apply, smul_eq_mul, MPSTensor.mpvOverlap]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem transferMap_A_diagonal (x : Fin 2 → ℂ) :
    MPSTensor.transferMap A (Matrix.diagonal x) =
      Matrix.diagonal (wMat.mulVec x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MPSTensor.transferMap_apply, A, wMat,
      dotProduct, Fin.sum_univ_four, Fin.sum_univ_two] <;> ring

private theorem transferMap_A_pow_single_diag (N : ℕ) (i : Fin 2) :
    (MPSTensor.transferMap A ^ N) (Matrix.single i i 1) =
      Matrix.diagonal (fun j ↦ (wMat ^ N) j i) := by
  induction N with
  | zero =>
      ext j k
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp [Matrix.single, Matrix.one_apply]
  | succ N ih =>
      rw [pow_succ', Module.End.mul_apply, ih, transferMap_A_diagonal]
      ext j k
      by_cases hjk : j = k
      · subst k
        simp only [Matrix.diagonal_apply_eq]
        rw [show wMat ^ (N + 1) = wMat * wMat ^ N by exact pow_succ' wMat N,
          Matrix.mul_apply]
        rfl
      · simp [Matrix.diagonal_apply_ne _ hjk]

private theorem transferMap_A_single_offdiag (i j : Fin 2) (hij : i ≠ j) :
    MPSTensor.transferMap A (Matrix.single i j 1) = 0 := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact transferMap_A_single01
  · exact transferMap_A_single10
  · exact (hij rfl).elim

private theorem transferMap_A_pow_single_offdiag
    (L : ℕ) (hL : 0 < L) (i j : Fin 2) (hij : i ≠ j) :
    (MPSTensor.transferMap A ^ L) (Matrix.single i j 1) = 0 := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
  rw [pow_succ, Module.End.mul_apply, transferMap_A_single_offdiag i j hij, map_zero]

/-- The self-overlap of `A` is the trace of the explicit two-dimensional local factor. -/
theorem mpvOverlap_A_eq_wMat_pow_trace (L : ℕ) (hL : 0 < L) :
    MPSTensor.mpvOverlap A A L = (wMat ^ L).trace := by
  rw [← MPSTensor.trace_mixedTransferMap_pow_eq_mpvOverlap A A L,
    MPSTensor.mixedTransferMap_self]
  rw [MPSTensor.linearMap_trace_eq_sum_apply_single]
  simp only [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j : Fin 2,
        ((MPSTensor.transferMap A ^ L) (Matrix.single i j 1)) i j) =
        ((MPSTensor.transferMap A ^ L) (Matrix.single i i 1)) i i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [transferMap_A_pow_single_offdiag L hL i j hji.symm]
        simp
      · simp
    _ = (wMat ^ L) i i := by
      rw [transferMap_A_pow_single_diag]
      simp

private theorem oneLabel_sameLengthProduct :
    (verticalBNTOperatorFamily (D := 4) oneLabelVerticalFamily).HasSameLengthProductForm
      oneLabelCoeffs := by
  intro L hL α β
  fin_cases α
  fin_cases β
  simp only [verticalBNTOperatorFamily_operator, oneLabelVerticalFamily,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  rw [mpo_verticalBNTMPO_verticalComponent, pureState_mul_self,
    mpvOverlap_A_eq_wMat_pow_trace L hL,
    ← oneLabelCoeffs_coeff_eq_wMat_pow_trace L hL]
  congr 2

private theorem oneLabel_idempotent :
    (verticalBNTTraceScalarFamily oneLabelWeight).HasIdempotentCoefficientForm
      oneLabelCoeffs := by
  intro γ
  fin_cases γ
  simp only [verticalBNTTraceScalarFamily_traceScalar, oneLabelWeight,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  change (25 / 32 : ℂ) = oneLabelCoeffs.coeff 1 0 0 0 *
    ((25 / 32 : ℂ) * (25 / 32 : ℂ))
  rw [oneLabelCoeffs_coeff]
  norm_num [lambda]

private noncomputable def R_oneLabelAlgebraClause :
    BNTAlgebraClause oneLabelCoeffs
      (verticalBNTOperatorFamily (D := 4) oneLabelVerticalFamily)
      (verticalBNTTraceScalarFamily oneLabelWeight) where
  positiveChi := oneLabelChiTracePowerForm
  sameLengthProduct := oneLabel_sameLengthProduct
  idempotent := oneLabel_idempotent

/-- The complete explicit one-label BNT algebra tensor clause for `R`. -/
noncomputable def R_oneLabelBNTAlgebraTensorClause : BNTAlgebraTensorClause R where
  labelCount := 1
  bondDim := oneLabelBondDim
  multiplicity := oneLabelMultiplicity
  weight := oneLabelWeight
  tensor := oneLabelVerticalFamily
  verticalCoisometry := oneLabelVerticalCoisometry
  multiplicity_pos := oneLabelMultiplicity_pos
  weight_pos := oneLabelWeight_pos
  coisometry := oneLabelVerticalCoisometry_coisometry
  isCPSVBNT := verticalComponent_isCPSVBasisOfNormalTensors
  forward := R_vertical_forward
  reconstruction := R_vertical_reconstruction
  coeffs := oneLabelCoeffs
  algebraClause := R_oneLabelAlgebraClause

/-- The rescaling-stable tensor has a BNT algebra tensor clause, witnessed by the explicit
one-label vertical clause.

Source: CPSV16, Theorem 4.14(i)--(ii), lines 972--985, and Appendix C.4,
lines 1929--2085. -/
theorem R_hasBNTAlgebraTensorClause : HasBNTAlgebraTensorClause R :=
  ⟨R_oneLabelBNTAlgebraTensorClause⟩

/-- The explicit BNT algebra tensor clause for `R` has one label. -/
@[simp] theorem R_oneLabelBNTAlgebraTensorClause_labelCount :
    R_oneLabelBNTAlgebraTensorClause.labelCount = 1 := rfl

/-- The tensor in the unique BNT label is the normalized vertical component. -/
@[simp] theorem R_oneLabelBNTAlgebraTensorClause_tensor (α : Fin 1) :
    R_oneLabelBNTAlgebraTensorClause.tensor α = verticalComponent := rfl

/-- The unique vertical multiplicity weight is `25/32`. -/
@[simp] theorem R_oneLabelBNTAlgebraTensorClause_weight (α : Fin 1) (q : Fin 1) :
    R_oneLabelBNTAlgebraTensorClause.weight α q = 25 / 32 := rfl

/-- The explicit clause uses the coefficient family `oneLabelCoeffs`. -/
@[simp] theorem R_oneLabelBNTAlgebraTensorClause_coeffs :
    R_oneLabelBNTAlgebraTensorClause.coeffs = oneLabelCoeffs := rfl

/-- The positive trace-power family in the explicit clause is `oneLabelChi`. -/
@[simp] theorem R_oneLabelBNTAlgebraTensorClause_chi :
    R_oneLabelBNTAlgebraTensorClause.algebraClause.positiveChi.chi = oneLabelChi := rfl

end MPOTensor.RescalingStableLengthDependentRFP
