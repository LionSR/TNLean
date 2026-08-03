/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.SingleSector
import TNLean.MPS.MPDO.ActiveSectorSpanningAreaLaw
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.BiCFDerivation.Core
import TNLean.MPS.MPDO.NormalizedMPOProportionality
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPDO.SimpleTensor
import TNLean.MPS.SharedInfra.Scaling

/-!
# The four-sector tensor at the blocking-channel boundary

This file puts the four-sector tensor of
`ActiveSectorSpanningCounterexample` in the scalar normalization required by
the horizontal canonical form of arXiv:1606.00608.  The normalized tensor
still has strong area law and source zero correlation length, but its
two-site block cannot be a renormalization fixed point in the sense of
Definition 4.1: its physical-trace transfer is a nonunit scalar multiple of
an idempotent.

## Reference

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.9 and Appendix C.2, lines 1484--1499 and 1810--1825
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor.ActiveSectorSpanningCounterexample

/-- The positive scalar which normalizes the horizontal transfer radius of
the four-sector tensor to one.

This implements the horizontal canonical normalization required in
arXiv:1606.00608, Definition 2.4 and Theorem 4.9, lines 217--226 and
849--856. -/
def canonicalScale : ℝ := 4 / Real.sqrt 5

/-- The horizontally normalized representative of the four-sector tensor.

Source boundary: arXiv:1606.00608, Theorem 4.9, lines 849--856. -/
def canonicalTensor : MPOTensor 4 2 :=
  (canonicalScale : ℂ) • tensor

lemma canonicalScale_pos : 0 < canonicalScale := by
  unfold canonicalScale
  positivity

lemma canonicalScale_ne_zero : (canonicalScale : ℂ) ≠ 0 := by
  exact_mod_cast canonicalScale_pos.ne'

lemma canonicalScale_sq : canonicalScale ^ 2 = 16 / 5 := by
  rw [canonicalScale, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

lemma coe_canonicalScale_sq : (canonicalScale : ℂ) ^ 2 = 16 / 5 := by
  rw [← Complex.ofReal_pow, canonicalScale_sq, Complex.ofReal_div]
  norm_num

@[simp] lemma star_canonicalScale :
    star (canonicalScale : ℂ) = (canonicalScale : ℂ) :=
  Complex.conj_ofReal canonicalScale

/-- The diagonal bond gauge which puts the canonical representative in
left-canonical form.

The gauge realizes the canonical-form normalization of arXiv:1606.00608,
Definition 2.4, lines 217--226, for this explicit tensor. -/
def canonicalGaugeMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![8, 0; 0, 1]

private lemma canonicalGaugeMatrix_det_ne_zero : canonicalGaugeMatrix.det ≠ 0 := by
  norm_num [canonicalGaugeMatrix, Matrix.det_fin_two]

/-- The canonical gauge as an invertible matrix.

Source boundary: arXiv:1606.00608, Definition 2.4, lines 217--226. -/
def canonicalGauge : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero canonicalGaugeMatrix
    canonicalGaugeMatrix_det_ne_zero

@[simp] lemma canonicalGauge_val :
    (canonicalGauge : Matrix (Fin 2) (Fin 2) ℂ) = canonicalGaugeMatrix :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

@[simp] lemma canonicalGauge_inv_val :
    ((canonicalGauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1 / 8, 0; 0, 1] := by
  have h : canonicalGauge * Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![1 / 8, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
      (by norm_num [Matrix.det_fin_two]) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [canonicalGaugeMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  rw [show canonicalGauge⁻¹ = Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![1 / 8, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
      (by norm_num [Matrix.det_fin_two]) from inv_eq_of_mul_eq_one_right h]
  exact Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

/-- The gauge-equivalent left-canonical normal block used in the one-sector
BNT presentation.

Source boundary: arXiv:1606.00608, Definition 2.4 and the BNT decomposition,
lines 217--301. -/
def canonicalBlock : MPSTensor (4 * 4) 2 :=
  fun i ↦
    (canonicalGauge : Matrix (Fin 2) (Fin 2) ℂ) *
      canonicalTensor.toMPSTensor i *
        ((canonicalGauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)

lemma canonicalTensor_toMPSTensor_pair (i j : Fin 4) :
    canonicalTensor.toMPSTensor (finProdFinEquiv (i, j)) =
      if i = j then (canonicalScale : ℂ) • sectorMatrix i else 0 := by
  unfold MPOTensor.toMPSTensor
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  simp [canonicalTensor, tensor]

/-- The four nonzero physical slices after the canonical bond gauge, before
the common scalar normalization.

These are the explicit slices used to test the canonical-form hypotheses of
arXiv:1606.00608, Theorem 4.9, lines 849--856. -/
def canonicalSectorMatrix : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![
  !![1 / 4, 1 / 4; 1 / 8, 1 / 8],
  !![1 / 4, 1 / 4; -1 / 8, -1 / 8],
  !![1 / 4, -1 / 4; 1 / 8, -1 / 8],
  !![1 / 4, -1 / 4; -1 / 8, 1 / 8]]

private def sectorMatrixInCoordinates : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![
  !![1 / 4, 1 / 32; 1, 1 / 8],
  !![1 / 4, 1 / 32; -1, -1 / 8],
  !![1 / 4, -1 / 32; 1, -1 / 8],
  !![1 / 4, -1 / 32; -1, 1 / 8]]

private lemma sectorMatrix_eq_inCoordinates (i : Fin 4) :
    sectorMatrix i = sectorMatrixInCoordinates i := by
  ext x y
  fin_cases i <;> fin_cases x <;> fin_cases y <;>
    norm_num [sectorMatrixInCoordinates, sectorMatrix, leftPairing, rightPairing]

lemma canonicalBlock_pair (i j : Fin 4) :
    canonicalBlock (finProdFinEquiv (i, j)) =
      if i = j then (canonicalScale : ℂ) • canonicalSectorMatrix i else 0 := by
  simp only [canonicalBlock, canonicalGauge_val, canonicalGauge_inv_val,
    canonicalTensor_toMPSTensor_pair]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Matrix.mul_smul, Matrix.smul_mul]
    rw [sectorMatrix_eq_inCoordinates]
    ext x y
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      norm_num [canonicalSectorMatrix, sectorMatrixInCoordinates,
        canonicalGaugeMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [if_neg hij, if_neg hij, Matrix.mul_zero, Matrix.zero_mul]

/-- The literal CPSV canonical representative obtained by separating the
doubled physical index of the left-canonical normal block.

Source boundary: arXiv:1606.00608, BNT canonical form, lines 217--301, and
Theorem 4.9, lines 849--856. -/
def canonicalRepresentative : MPOTensor 4 2 :=
  verticalBNTMPO canonicalBlock

@[simp] lemma canonicalRepresentative_toMPSTensor :
    canonicalRepresentative.toMPSTensor = canonicalBlock :=
  verticalBNTMPO_toMPSTensor canonicalBlock

lemma canonicalTensor_gaugeEquiv_canonicalBlock :
    MPSTensor.GaugeEquiv canonicalTensor.toMPSTensor canonicalBlock :=
  ⟨canonicalGauge, fun _ ↦ rfl⟩

/-- The explicit bond gauge satisfies the left-canonical normalization of
arXiv:1606.00608, Definition 2.4, lines 217--226. -/
lemma canonicalBlock_isLeftCanonical :
    MPSTensor.IsLeftCanonical canonicalBlock := by
  unfold MPSTensor.IsLeftCanonical
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp_rw [canonicalBlock_pair]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalSectorMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four, Fin.sum_univ_two] <;>
    norm_num [starRingEnd_apply] <;>
    ring_nf <;>
    norm_num [coe_canonicalScale_sq]

lemma canonicalTensor_isInjective : canonicalTensor.IsInjective := by
  change MPSTensor.IsInjective
    (fun i ↦ (canonicalScale : ℂ) • tensor.toMPSTensor i)
  exact tensor_isInjective.smul canonicalScale_ne_zero

lemma canonicalBlock_isInjective : canonicalBlock.IsInjective :=
  MPSTensor.isInjective_of_gaugeEquiv canonicalTensor_isInjective
    canonicalTensor_gaugeEquiv_canonicalBlock

lemma canonicalBlock_isNormalTensor :
    MPSTensor.IsNormalTensor canonicalBlock :=
  MPSTensor.isNormalTensor_of_isNormal_leftCanonical canonicalBlock
    canonicalBlock_isInjective.isNormal canonicalBlock_isLeftCanonical

/-- The one-block decomposition satisfies the BNT hypotheses of
arXiv:1606.00608, Section 2.3, lines 217--301. -/
lemma canonicalBlock_isBNTCanonicalForm :
    MPSTensor.IsBNTCanonicalForm
      (MPSTensor.singleSectorDecomposition canonicalBlock) := by
  apply MPSTensor.isBNTCanonicalForm_singleSectorDecomposition
    canonicalBlock_isNormalTensor.no_invariant_proj
    canonicalBlock_isLeftCanonical
  exact MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
    canonicalBlock canonicalBlock_isNormalTensor.no_invariant_proj
      canonicalBlock_isLeftCanonical canonicalBlock_isNormalTensor.primitive_transfer

/-- The literal representative is in the canonical form assumed by
arXiv:1606.00608, Theorem 4.9, lines 849--856. -/
lemma canonicalRepresentative_isCPSVCanonicalForm :
    MPSTensor.IsCPSVCanonicalForm canonicalRepresentative.toMPSTensor := by
  rw [canonicalRepresentative_toMPSTensor,
    ← MPSTensor.toTensorFromBlocks_fin_one canonicalBlock]
  exact (MPSTensor.CPSVCanonicalFormData.ofBlocks
    (fun _ : Fin 1 ↦ by simp) (fun _ : Fin 1 ↦ (1 : ℂ))
      (fun _ : Fin 1 ↦ canonicalBlock)
      (fun _ ↦ canonicalBlock_isNormalTensor)).isCPSVCanonicalForm

/-- The single normal block is block-injective already at word length one,
meeting the biCF hypothesis used in arXiv:1606.00608, Appendix C.2,
lines 1628--1658. -/
lemma canonicalBlock_hasBiCF :
    MPSTensor.HasBiCF (fun _ : Fin 1 ↦ canonicalBlock) :=
  canonicalBlock_isInjective.hasBiCF_fin_one

lemma canonicalBlock_singleSector_hasBiCF :
    MPSTensor.HasBiCF
      (MPSTensor.singleSectorDecomposition canonicalBlock).basis := by
  simpa [MPSTensor.singleSectorDecomposition] using canonicalBlock_hasBiCF

lemma mpo_canonicalTensor (N : ℕ) :
    mpo canonicalTensor N = ((canonicalScale : ℂ) ^ N) • mpo tensor N := by
  ext σ τ
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig,
    ← MPSTensor.mpv_toMPSTensor_pairConfig]
  change MPSTensor.mpv
    (fun i ↦ (canonicalScale : ℂ) • tensor.toMPSTensor i)
      (fun n ↦ finProdFinEquiv (σ n, τ n)) =
    (canonicalScale : ℂ) ^ N *
      MPSTensor.mpv tensor.toMPSTensor
        (fun n ↦ finProdFinEquiv (σ n, τ n))
  rw [MPSTensor.mpv_smul]

lemma mpo_canonicalRepresentative (N : ℕ) :
    mpo canonicalRepresentative N = mpo canonicalTensor N := by
  ext σ τ
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig,
    ← MPSTensor.mpv_toMPSTensor_pairConfig,
    canonicalRepresentative_toMPSTensor]
  exact (canonicalTensor_gaugeEquiv_canonicalBlock.sameMPV N _).symm

/-- The normalized tensor generates positive operators, as required in
arXiv:1606.00608, Theorem 4.9, lines 849--856. -/
lemma canonicalTensor_isMPDO : IsMPDO canonicalTensor := by
  intro N hN
  rw [mpo_canonicalTensor]
  apply (Classical.choose tensor_isSAL N hN).smul
  exact_mod_cast pow_nonneg canonicalScale_pos.le N

/-- The literal canonical representative generates the same positive operator
family and hence satisfies the MPDO hypothesis of arXiv:1606.00608,
Theorem 4.9, lines 849--856. -/
lemma canonicalRepresentative_isMPDO : IsMPDO canonicalRepresentative := by
  intro N hN
  rw [mpo_canonicalRepresentative]
  exact canonicalTensor_isMPDO N hN

lemma normalizedMPO_canonicalTensor (N : ℕ) :
    normalizedMPO canonicalTensor N = normalizedMPO tensor N := by
  apply normalizedMPO_eq_of_nonzeroProportionalMPV₂_at
  refine ⟨(canonicalScale : ℂ) ^ N, pow_ne_zero N canonicalScale_ne_zero, ?_⟩
  intro ρ
  change MPSTensor.mpv (fun i ↦ (canonicalScale : ℂ) • tensor.toMPSTensor i) ρ = _
  rw [MPSTensor.mpv_smul]

lemma normalizedMPO_canonicalRepresentative (N : ℕ) :
    normalizedMPO canonicalRepresentative N = normalizedMPO tensor N := by
  rw [normalizedMPO, mpo_canonicalRepresentative,
    ← normalizedMPO, normalizedMPO_canonicalTensor]

/-- Scalar normalization preserves the strong area law appearing in
arXiv:1606.00608, Theorem 4.9(ii), lines 851--856. -/
lemma canonicalTensor_isSAL : IsSAL canonicalTensor := by
  rcases tensor_isSAL with ⟨_, hTrace, hStep⟩
  refine ⟨canonicalTensor_isMPDO, ?_, ?_⟩
  · intro N hN
    rw [mpo_canonicalTensor, Matrix.trace_smul]
    exact mul_ne_zero (pow_ne_zero N canonicalScale_ne_zero) (hTrace N hN)
  · intro N L hL hLN
    simpa only [mutualInfoChain, blockEntropy, reducedBlockState,
      normalizedMPO_canonicalTensor] using hStep N L hL hLN

/-- Gauge transport preserves the strong area law of
arXiv:1606.00608, Theorem 4.9(ii), lines 851--856. -/
lemma canonicalRepresentative_isSAL : IsSAL canonicalRepresentative := by
  rcases canonicalTensor_isSAL with ⟨_, hTrace, hStep⟩
  refine ⟨canonicalRepresentative_isMPDO, ?_, ?_⟩
  · intro N hN
    rw [mpo_canonicalRepresentative]
    exact hTrace N hN
  · intro N L hL hLN
    simpa only [mutualInfoChain, blockEntropy, reducedBlockState,
      normalizedMPO_canonicalRepresentative, normalizedMPO_canonicalTensor] using
        hStep N L hL hLN

/-- The physical-trace transfer of the canonical representative is the same
rank-one projection as for `tensor`, multiplied by the canonical scalar. -/
lemma physTraceTransfer_canonicalTensor :
    physTraceTransfer canonicalTensor =
      (canonicalScale : ℂ) • !![1, 0; 0, 0] := by
  rw [canonicalTensor]
  change ∑ i : Fin 4, (canonicalScale : ℂ) • tensor i i = _
  rw [← Finset.smul_sum, ← physTraceTransfer]
  rw [physTraceTransfer_tensor, leftPairing_mul_rightPairing]

/-- The normalized tensor satisfies the scale-invariant zero-correlation
condition of arXiv:1606.00608, Theorem 4.9(ii), lines 851--856. -/
lemma canonicalTensor_isSourceZCL : IsSourceZCL canonicalTensor := by
  refine ⟨?_, canonicalScale, canonicalScale_pos, ?_⟩
  · rw [physTraceTransfer_canonicalTensor]
    intro hzero
    have h00 := congrFun (congrFun hzero (0 : Fin 2)) (0 : Fin 2)
    simp at h00
    exact canonicalScale_pos.ne' h00
  · rw [physTraceTransfer_canonicalTensor,
      smul_mul_smul_comm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp

lemma physTraceTransfer_canonicalRepresentative :
    physTraceTransfer canonicalRepresentative =
      (canonicalScale : ℂ) • !![1, 0; 0, 0] := by
  rw [physTraceTransfer]
  simp only [canonicalRepresentative, verticalBNTMPO_apply]
  simp_rw [canonicalBlock_pair]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalSectorMatrix, Fin.sum_univ_four] <;> ring

/-- The literal canonical representative satisfies the source ZCL condition
of arXiv:1606.00608, Theorem 4.9(ii), lines 851--856. -/
lemma canonicalRepresentative_isSourceZCL :
    IsSourceZCL canonicalRepresentative := by
  refine ⟨?_, canonicalScale, canonicalScale_pos, ?_⟩
  · rw [physTraceTransfer_canonicalRepresentative]
    intro hzero
    have h00 := congrFun (congrFun hzero (0 : Fin 2)) (0 : Fin 2)
    simp at h00
    exact canonicalScale_pos.ne' h00
  · rw [physTraceTransfer_canonicalRepresentative,
      smul_mul_smul_comm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp

lemma doubledPhysTraceTransfer_canonicalBlock :
    doubledPhysTraceTransfer 4 canonicalBlock =
      (canonicalScale : ℂ) • !![1, 0; 0, 0] := by
  rw [doubledPhysTraceTransfer]
  simp_rw [canonicalBlock_pair]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalSectorMatrix, Fin.sum_univ_four] <;> ring

lemma doubledPhysTraceTransfer_canonicalBlock_not_isNilpotent :
    ¬ IsNilpotent (doubledPhysTraceTransfer 4 canonicalBlock) := by
  intro hnil
  have htrace := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  rw [doubledPhysTraceTransfer_canonicalBlock] at htrace
  simp [Matrix.trace, Fin.sum_univ_two] at htrace
  exact canonicalScale_pos.ne' htrace

/-- The canonical representative is simple in the one-sector BNT canonical
form used in the standing hypotheses of arXiv:1606.00608, Theorem 4.9,
lines 815--856. -/
lemma canonicalRepresentative_isSimpleCanonicalForm :
    IsSimpleCanonicalForm canonicalRepresentative := by
  let S := MPSTensor.singleSectorDecomposition canonicalBlock
  refine ⟨canonicalRepresentative_isMPDO, S,
    canonicalBlock_isBNTCanonicalForm, ?_, ?_⟩
  · intro j
    fin_cases j
    simpa [S, MPSTensor.singleSectorDecomposition] using
      doubledPhysTraceTransfer_canonicalBlock_not_isNilpotent
  · have hTotal : S.totalDim = 2 := by
      rfl
    refine ⟨hTotal, fun _ ↦ 1, ?_⟩
    intro i
    rw [canonicalRepresentative_toMPSTensor]
    have hGaugeOne :
        MPSTensor.globalGaugeOfBlocks (dim := S.flatDim) (fun _ ↦ 1) = 1 := by
      exact MPSTensor.globalGaugeOfBlocks_one
    rw [hGaugeOne]
    simp only [Units.val_one, inv_one, one_mul, mul_one]
    change canonicalBlock i = S.toTensor i
    change canonicalBlock i = MPSTensor.toTensorFromBlocks
      (fun _ : Fin 1 ↦ (1 : ℂ)) (fun _ : Fin 1 ↦ canonicalBlock) i
    exact congrFun (MPSTensor.toTensorFromBlocks_fin_one canonicalBlock) i |>.symm

/-- Blocking two sites squares the canonical scalar and leaves the idempotent
physical-trace transfer of the unscaled tensor unchanged. -/
lemma physTraceTransfer_blockTwo_canonicalTensor :
    physTraceTransfer (blockTwo canonicalTensor) =
      ((canonicalScale : ℂ) ^ 2) • !![1, 0; 0, 0] := by
  rw [physTraceTransfer_blockTwo, physTraceTransfer_canonicalTensor,
    smul_mul_smul_comm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two]

/-- The two-site block of the horizontally normalized four-sector tensor is
not a renormalization fixed point via the trace-preserving completely positive
maps of Definition 4.1.

The obstruction is normalization-sensitive and does not use the invalid
rank-one inference of Lemma C.5: trace preservation would make the blocked
physical-trace transfer idempotent, whereas its nonzero eigenvalue is
`canonicalScale ^ 2 = 16 / 5`.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Theorem 4.9,
direction (ii) implies (v), lines 851--893. -/
theorem blockTwo_canonicalTensor_not_isRFPViaTS :
    ¬ IsRFPViaTS (blockTwo canonicalTensor) := by
  intro hRFP
  have hidem := physTraceTransfer_sq_of_isRFPViaTS _ hRFP
  rw [physTraceTransfer_blockTwo_canonicalTensor] at hidem
  have h00 := congrFun (congrFun hidem (0 : Fin 2)) (0 : Fin 2)
  norm_num [coe_canonicalScale_sq, Matrix.mul_apply, Fin.sum_univ_two] at h00

lemma physTraceTransfer_blockTwo_canonicalRepresentative :
    physTraceTransfer (blockTwo canonicalRepresentative) =
      ((canonicalScale : ℂ) ^ 2) • !![1, 0; 0, 0] := by
  rw [physTraceTransfer_blockTwo, physTraceTransfer_canonicalRepresentative,
    smul_mul_smul_comm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two]

/-- The two-site block of the literal CPSV canonical representative is not a
renormalization fixed point via the trace-preserving completely positive maps
of Definition 4.1. -/
theorem blockTwo_canonicalRepresentative_not_isRFPViaTS :
    ¬ IsRFPViaTS (blockTwo canonicalRepresentative) := by
  intro hRFP
  have hidem := physTraceTransfer_sq_of_isRFPViaTS _ hRFP
  rw [physTraceTransfer_blockTwo_canonicalRepresentative] at hidem
  have h00 := congrFun (congrFun hidem (0 : Fin 2)) (0 : Fin 2)
  norm_num [coe_canonicalScale_sq, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The literal one-sector CPSV representative satisfies the standing simple,
BNT, and biCF conditions of Theorem 4.9 together with SAL and source ZCL, but
its two-site block is not an RFP via the two channels of Definition 4.1.

Thus the printed implication (ii) to (v) is false, rather than merely missing
the rank-one proof supplied through Lemma C.5.  The obstruction and the
normalization-sensitive representative are documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Theorem 4.9, lines 849--893; Appendix C.2,
Lemma C.5, lines 1484--1499; and `prop2to5`, lines 1810--1825. -/
theorem canonicalRepresentative_refutes_theorem4_9_ii_to_v :
    MPSTensor.IsCPSVCanonicalForm canonicalRepresentative.toMPSTensor ∧
      IsSimpleCanonicalForm canonicalRepresentative ∧
      MPSTensor.IsBNTCanonicalForm
        (MPSTensor.singleSectorDecomposition canonicalBlock) ∧
      MPSTensor.HasBiCF
        (MPSTensor.singleSectorDecomposition canonicalBlock).basis ∧
      IsSAL canonicalRepresentative ∧
      IsSourceZCL canonicalRepresentative ∧
      ¬ IsRFPViaTS (blockTwo canonicalRepresentative) :=
  ⟨canonicalRepresentative_isCPSVCanonicalForm,
    canonicalRepresentative_isSimpleCanonicalForm,
    canonicalBlock_isBNTCanonicalForm,
    canonicalBlock_singleSector_hasBiCF,
    canonicalRepresentative_isSAL,
    canonicalRepresentative_isSourceZCL,
    blockTwo_canonicalRepresentative_not_isRFPViaTS⟩

end MPOTensor.ActiveSectorSpanningCounterexample
