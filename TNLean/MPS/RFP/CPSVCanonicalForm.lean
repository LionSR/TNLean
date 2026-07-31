/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.RFP.BNTOrthogonality
import TNLean.MPS.SharedInfra.Scaling
import TNLean.Spectral.Radius

/-!
# Active blocks of a literal CPSV renormalization fixed point

This file proves the first source-facing part of arXiv:1606.00608, Corollary 3.12
(lines 583--590), using the observation in its proof at line 1303 that every
active normal-tensor block of a renormalization fixed point is itself a
renormalization fixed point.
-/

open scoped Matrix BigOperators ENNReal

namespace MPSTensor

variable {d D : ℕ}

/-- Transfer idempotence is preserved and reflected by exact reconstruction through a
coisometry.

If `A i = Uᴴ * B i * U` and `U * Uᴴ = 1`, then the transfer maps of `A` and `B` are
idempotent simultaneously. This is the retained-support cancellation used for the literal
canonical form in arXiv:1606.00608, lines 214--225 and Corollary 3.12. -/
theorem isTransferIdempotent_coisometry_reconstruction_iff
    {R : ℕ} (A : MPSTensor d D) (B : MPSTensor d R)
    (U : Matrix (Fin R) (Fin D) ℂ) (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ i, A i = Uᴴ * B i * U) :
    IsTransferIdempotent A ↔ IsTransferIdempotent B := by
  have hTransfer : ∀ X,
      transferMap A X = Uᴴ * transferMap B (U * X * Uᴴ) * U := by
    intro X
    simp only [transferMap_apply, hReconstruct, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc
      _ = ∑ i, Uᴴ * (B i * (U * X * Uᴴ) * (B i)ᴴ) * U := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Matrix.mul_assoc]
      _ = Uᴴ * (∑ i, B i * (U * X * Uᴴ) * (B i)ᴴ) * U := by
        symm
        rw [Matrix.mul_sum, Matrix.sum_mul]
  have hCancel : ∀ Y : Matrix (Fin R) (Fin R) ℂ,
      U * (Uᴴ * Y * U) * Uᴴ = Y := by
    intro Y
    calc
      U * (Uᴴ * Y * U) * Uᴴ = (U * Uᴴ) * Y * (U * Uᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = Y := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  constructor
  · intro hA
    change transferMap B ∘ₗ transferMap B = transferMap B
    apply LinearMap.ext
    intro Y
    have hAY := LinearMap.congr_fun hA (Uᴴ * Y * U)
    simp only [LinearMap.comp_apply, hTransfer, hCancel] at hAY
    have h := congrArg (fun Z => U * Z * Uᴴ) hAY
    simpa only [LinearMap.comp_apply, hCancel] using h
  · intro hB
    change transferMap A ∘ₗ transferMap A = transferMap A
    apply LinearMap.ext
    intro X
    have hBX := LinearMap.congr_fun hB (U * X * Uᴴ)
    simpa only [LinearMap.comp_apply, hTransfer, hCancel] using
      congrArg (fun Y => Uᴴ * Y * U) hBX

/-- A nonzero scalar multiple of a normal tensor can have idempotent transfer map only when
that scalar has norm one. In that case the original normal block is transfer-idempotent too.

The proof uses the spectral-radius-one Perron normalization in the definition of a normal
tensor (arXiv:1606.00608, lines 224--235) and the diagonal transfer-idempotence equation from
Corollary 3.12, lines 583--590. -/
theorem norm_eq_one_and_isTransferIdempotent_of_isNormalTensor_smul
    {R : ℕ} (A : MPSTensor d R) (hA : IsNormalTensor A)
    (c : ℂ) (hc : c ≠ 0)
    (hRFP : IsTransferIdempotent (fun i => c • A i)) :
    ‖c‖ = 1 ∧ IsTransferIdempotent A := by
  letI : NeZero R := ⟨hA.bondDim_ne_zero⟩
  let E := transferMap A
  let Eclm := (Module.End.toContinuousLinearMap (Matrix (Fin R) (Fin R) ℂ)) E
  let q := c * starRingEnd ℂ c
  have hq : q ≠ 0 := mul_ne_zero hc ((map_ne_zero (starRingEnd ℂ)).2 hc)
  have hMap : transferMap (fun i => c • A i) = q • E := by
    apply LinearMap.ext
    intro X
    rw [transferMap_smul]
    rfl
  have hEclm_ne : Eclm ≠ 0 := by
    intro hzero
    have hrad := hA.spectral_radius_one
    change spectralRadius ℂ Eclm = 1 at hrad
    rw [hzero, spectrum.spectralRadius_zero] at hrad
    exact zero_ne_one hrad
  have hqEclm_ne : q • Eclm ≠ 0 := smul_ne_zero hq hEclm_ne
  have hIdem : IsIdempotentElem (q • Eclm) := by
    have hEnd : IsIdempotentElem (transferMap (fun i => c • A i)) := hRFP
    have hMapped := hEnd.map (Module.End.toContinuousLinearMap
      (Matrix (Fin R) (Fin R) ℂ))
    simpa only [hMap, map_smul, Eclm] using hMapped
  have hradScaled : spectralRadius ℂ (q • Eclm) = 1 :=
    IsIdempotentElem.spectralRadius_eq_one_of_ne_zero hIdem hqEclm_ne
  have hscale := spectralRadius_smul Eclm hq
  have hradE : spectralRadius ℂ Eclm = 1 := hA.spectral_radius_one
  have hqNormENN : (‖q‖₊ : ℝ≥0∞) = 1 := by
    calc
      (‖q‖₊ : ℝ≥0∞) =
          (‖q‖₊ : ℝ≥0∞) * spectralRadius ℂ Eclm := by
        rw [hradE, mul_one]
      _ = spectralRadius ℂ (q • Eclm) := hscale.symm
      _ = 1 := hradScaled
  have hqNormNN : ‖q‖₊ = 1 := ENNReal.coe_injective hqNormENN
  have hqNorm : ‖q‖ = 1 := congrArg Subtype.val hqNormNN
  have hcSq : ‖c‖ * ‖c‖ = 1 := by
    simpa only [q, norm_mul, RCLike.star_def, RCLike.norm_conj] using hqNorm
  have hcNorm : ‖c‖ = 1 := by
    nlinarith [norm_nonneg c]
  refine ⟨hcNorm, ?_⟩
  have hqOne : q = 1 := by
    simpa [q, RCLike.star_def, Complex.normSq_eq_norm_sq, hcNorm] using
      Complex.mul_conj c
  rw [IsTransferIdempotent, hMap, hqOne, one_smul] at hRFP
  exact hRFP

namespace CPSVCanonicalFormData

/-- Every active listed block of a literal CPSV canonical-form renormalization fixed point has
unit-modulus weight and is itself a renormalization fixed point.

This is the active-block consequence of arXiv:1606.00608, Corollary 3.12, lines 583--590,
with the proof observation at line 1303.

**Scope restriction (active canonical blocks):** the printed assertion concerns arbitrary BNT
members, whereas literal BNT data may contain unused zero-coefficient members. This theorem
therefore restricts to `data.Active`; see `docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`. -/
theorem active_weight_norm_one_and_block_rfp
    (data : CPSVCanonicalFormData A) (hRFP : IsTransferIdempotent A)
    (k : data.Active) :
    ‖data.weights k‖ = 1 ∧ IsTransferIdempotent (data.blocks k) := by
  letI : ∀ j : Fin data.r, NeZero (data.dim j) :=
    fun j => ⟨Nat.ne_of_gt (data.dim_pos j)⟩
  let scaledBlocks : (j : Fin data.r) → MPSTensor _ (data.dim j) :=
    fun j i => data.weights j • data.blocks j i
  have hRetained :
      IsTransferIdempotent (toTensorFromBlocks data.weights data.blocks) :=
    (isTransferIdempotent_coisometry_reconstruction_iff A
      (toTensorFromBlocks data.weights data.blocks)
      data.ambient_coisometry data.coisometric data.reconstruct).mp hRFP
  change IsTransferIdempotent (directSumTensor scaledBlocks) at hRetained
  have hScaledBlock :=
    mixedTransferMap₂_isIdempotentElem_of_isTransferIdempotent_directSum
      scaledBlocks hRetained k k
  rw [mixedTransferMap₂_self] at hScaledBlock
  exact norm_eq_one_and_isTransferIdempotent_of_isNormalTensor_smul
    (data.blocks k) (data.blocks_normal k) (data.weights k) k.property hScaledBlock

end CPSVCanonicalFormData

end MPSTensor
