/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ActiveBNTRefinement
import TNLean.MPS.FundamentalTheorem.Multi
import TNLean.MPS.RFP.BNTDirectSumBasis
import TNLean.MPS.RFP.NormalIsometryCharacterization
import TNLean.MPS.RFP.ResidualIsometry
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

/-- Removing nonzero scalar factors from both legs preserves gauge-phase equivalence. -/
private theorem gaugePhaseEquiv_of_smul
    {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {c e : ℂ} (hc : c ≠ 0) (he : e ≠ 0) (hdim : D₁ = D₂)
    (h : GaugePhaseEquiv
      (cast (congr_arg (MPSTensor d) hdim) (fun i => c • A i))
      (fun i => e • B i)) :
    GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hdim) A) B := by
  subst D₂
  obtain ⟨X, ζ, hζ, hrel⟩ := h
  refine ⟨X, e⁻¹ * ζ * c, mul_ne_zero (mul_ne_zero (inv_ne_zero he) hζ) hc, ?_⟩
  intro i
  have hrel_i := hrel i
  simp only [cast_eq] at hrel_i ⊢
  calc
    B i = e⁻¹ • (e • B i) := by simp [he]
    _ = e⁻¹ • (ζ • ((X : Matrix (Fin D₁) (Fin D₁) ℂ) * (c • A i) *
          (↑(X⁻¹) : Matrix (Fin D₁) (Fin D₁) ℂ))) := by rw [hrel_i]
    _ = (e⁻¹ * ζ * c) • ((X : Matrix (Fin D₁) (Fin D₁) ℂ) * A i *
          (↑(X⁻¹) : Matrix (Fin D₁) (Fin D₁) ℂ)) := by
      simp only [smul_smul, Algebra.mul_smul_comm, Matrix.coe_units_inv,
        Algebra.smul_mul_assoc]
      rw [← mul_assoc]

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
    isTransferIdempotent_block_of_isTransferIdempotent_directSum
      scaledBlocks hRetained k
  exact norm_eq_one_and_isTransferIdempotent_of_isNormalTensor_smul
    (data.blocks k) (data.blocks_normal k) (data.weights k) k.property hScaledBlock

namespace ActiveBNTRefinement

/-- The chosen active phase-class representatives of a literal CPSV canonical-form
renormalization fixed point have simultaneous square-root isometry canonical forms, and their
residual tensors satisfy the full joint residual-isometry equation.

Only nonzero-weight active classes occur. Distinct representatives are separated by
`representativesNotEquiv`; the idempotence of every mixed active pair is inherited from the
retained direct sum. After independent trace-preserving Perron gauges, the mixed spectral gap
forces each off-diagonal map to vanish. The conclusion includes the empty active family.

The square-root diagonal follows TNLean's corrected convention for arXiv:1606.00608,
Corollary `III.cor3`, lines 583--590; see `IsIsometryCanonicalForm`. -/
theorem exists_residualIsometryFamily_of_isTransferIdempotent
    {data : CPSVCanonicalFormData A} (ref : data.ActiveBNTRefinement)
    (hRFP : IsTransferIdempotent A) :
    ∃ (X : (j : Fin data.activePhaseClasses.g) →
        Matrix (Fin (data.dim (data.activeRepresentativeIndex j)))
          (Fin (data.dim (data.activeRepresentativeIndex j))) ℂ)
      (Λ : (j : Fin data.activePhaseClasses.g) →
        Fin (data.dim (data.activeRepresentativeIndex j)) → ℝ)
      (U : (j : Fin data.activePhaseClasses.g) →
        MPSTensor d (data.dim (data.activeRepresentativeIndex j))),
      (∀ j, (X j).det ≠ 0) ∧
      (∀ j k, 0 < Λ j k) ∧
      (∀ j, ∑ k, Λ j k = 1) ∧
      (∀ j i, data.blocks (data.activeRepresentativeIndex j) i =
        X j * Matrix.diagonal (fun k => (Real.sqrt (Λ j k) : ℂ)) *
          U j i * (X j)⁻¹) ∧
      IsResidualIsometryFamily U := by
  classical
  let repDim : Fin data.activePhaseClasses.g → ℕ :=
    fun j => data.dim (data.activeRepresentativeIndex j)
  let B : (j : Fin data.activePhaseClasses.g) → MPSTensor d (repDim j) :=
    fun j => data.blocks (data.activeRepresentativeIndex j)
  let μ : Fin data.activePhaseClasses.g → ℂ :=
    fun j => data.weights (data.activeRepresentativeIndex j)
  let C : (j : Fin data.activePhaseClasses.g) → MPSTensor d (repDim j) :=
    fun j i => μ j • B j i
  letI : ∀ k : Fin data.r, NeZero (data.dim k) :=
    fun k => ⟨Nat.ne_of_gt (data.dim_pos k)⟩
  letI : ∀ j : Fin data.activePhaseClasses.g, NeZero (repDim j) :=
    fun j => ⟨Nat.ne_of_gt (data.dim_pos (data.activeRepresentativeIndex j))⟩
  have hμ : ∀ j, ‖μ j‖ = 1 := fun j =>
    (data.active_weight_norm_one_and_block_rfp hRFP
      (data.activeRepresentativeIndex j)).1
  have hμne : ∀ j, μ j ≠ 0 := fun j => Complex.ne_zero_of_norm_eq_one (hμ j)
  have hBRFP : ∀ j, IsTransferIdempotent (B j) := fun j =>
    (data.active_weight_norm_one_and_block_rfp hRFP
      (data.activeRepresentativeIndex j)).2
  have hBICF : ∀ j, IsIsometryCanonicalForm (B j) := fun j =>
    (ref.representativeNormal j).isTransferIdempotent_iff_isIsometryCanonicalForm.mp (hBRFP j)
  let allScaled : (k : Fin data.r) → MPSTensor d (data.dim k) :=
    fun k i => data.weights k • data.blocks k i
  have hRetained : IsTransferIdempotent (directSumTensor allScaled) := by
    have h := (isTransferIdempotent_coisometry_reconstruction_iff A
      (toTensorFromBlocks data.weights data.blocks)
      data.ambient_coisometry data.coisometric data.reconstruct).mp hRFP
    exact h
  have hCRFP : IsTransferIdempotent (directSumTensor C) :=
    (isTransferIdempotent_directSumTensor_iff_pairwise_mixedTransferMap₂_isIdempotentElem
      C).2 fun j k =>
        mixedTransferMap₂_isIdempotentElem_of_isTransferIdempotent_directSum
          allScaled hRetained (data.activeRepresentativeIndex j)
            (data.activeRepresentativeIndex k)
  choose σ hσ hσfix hTP hGauge hPrim hIrr using
    fun j => (ref.representativeNormal j).exists_tpGauge
  let P : (j : Fin data.activePhaseClasses.g) → MPSTensor d (repDim j) :=
    fun j i => μ j • tpGauge (B j) (σ j) i
  have hGaugeC : ∀ j, GaugeEquiv (C j) (P j) := by
    intro j
    obtain ⟨G, hG⟩ := hGauge j
    refine ⟨G, fun i => ?_⟩
    simp only [C, P, B]
    rw [hG i]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  have hGaugeDirect : GaugeEquiv (directSumTensor C) (directSumTensor P) := by
    rw [← toTensorFromBlocks_one_eq_directSumTensor C,
      ← toTensorFromBlocks_one_eq_directSumTensor P]
    exact gaugeEquiv_toTensorFromBlocks_of_blockGauge (fun _ => 1) C P hGaugeC
  have hPRFP : IsTransferIdempotent (directSumTensor P) :=
    hGaugeDirect.isTransferIdempotent_iff.mp hCRFP
  have hPIrr : ∀ j, IsIrreducibleTensor (P j) := fun j =>
    isIrreducibleTensor_smul (hμne j) _ (hIrr j)
  have hPLeft : ∀ j, IsLeftCanonical (P j) := fun j =>
    leftCanonical_smul_of_norm_one (μ j) (hμ j) _ (hTP j)
  have hPDistinct : BlocksNotGaugePhaseEquiv (d := d) P := by
    intro j k hjk hdim hGPE
    apply ref.representativesNotEquiv j k hjk hdim
    apply gaugePhaseEquiv_of_gaugeEquiv_left_right_cast hdim (hGauge j) _ (hGauge k)
    exact gaugePhaseEquiv_of_smul (hμne j) (hμne k) hdim hGPE
  have hPZero : IsBNTLocallyOrthogonal P :=
    isBNTLocallyOrthogonal_of_isTransferIdempotent_directSum
      P hPIrr hPLeft hPDistinct hPRFP
  have hBZero : ∀ j k, j ≠ k → mixedTransferMap₂ (B j) (B k) = 0 := by
    intro j k hjk
    have hCZero : mixedTransferMap₂ (C j) (C k) = 0 :=
      mixedTransferMap₂_eq_zero_of_gaugePhaseEquiv
        (hGaugeC j).toGaugePhaseEquiv (hGaugeC k).toGaugePhaseEquiv (hPZero j k hjk)
    rw [mixedTransferMap₂_smul] at hCZero
    exact (smul_eq_zero.mp hCZero).resolve_left
      (mul_ne_zero (hμne j) ((map_ne_zero (starRingEnd ℂ)).2 (hμne k)))
  simpa only [B, repDim] using
    exists_residualIsometryFamily_of_isIsometryCanonicalForm B hBICF hBZero

end ActiveBNTRefinement

end CPSVCanonicalFormData

namespace IsCPSVCanonicalForm

/-- Predicate-level form of the corrected active Corollary 3.12: for the canonical witness data
and its chosen active BNT refinement, the representative blocks possess simultaneous square-root
isometry forms with a joint residual-isometry family.

Source: arXiv:1606.00608, Corollary `III.cor3`, lines 583--590. -/
theorem exists_activeBNT_residualIsometryFamily
    (hCF : IsCPSVCanonicalForm A) (hRFP : IsTransferIdempotent A) :
    ∃ (X : (j : Fin hCF.data.activePhaseClasses.g) →
        Matrix (Fin (hCF.data.dim (hCF.data.activeRepresentativeIndex j)))
          (Fin (hCF.data.dim (hCF.data.activeRepresentativeIndex j))) ℂ)
      (Λ : (j : Fin hCF.data.activePhaseClasses.g) →
        Fin (hCF.data.dim (hCF.data.activeRepresentativeIndex j)) → ℝ)
      (U : (j : Fin hCF.data.activePhaseClasses.g) →
        MPSTensor d (hCF.data.dim (hCF.data.activeRepresentativeIndex j))),
      (∀ j, (X j).det ≠ 0) ∧
      (∀ j k, 0 < Λ j k) ∧
      (∀ j, ∑ k, Λ j k = 1) ∧
      (∀ j i, hCF.data.blocks (hCF.data.activeRepresentativeIndex j) i =
        X j * Matrix.diagonal (fun k => (Real.sqrt (Λ j k) : ℂ)) *
          U j i * (X j)⁻¹) ∧
      IsResidualIsometryFamily U := by
  let ref := CPSVCanonicalFormData.activeBNTRefinement hCF.data
  exact ref.exists_residualIsometryFamily_of_isTransferIdempotent hRFP

end IsCPSVCanonicalForm

end MPSTensor
