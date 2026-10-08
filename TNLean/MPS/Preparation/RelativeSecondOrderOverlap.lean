/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IdempotentTracePerturbation
import TNLean.MPS.Preparation.RelativePolarCompression

/-!
# Second-order overlaps of the relative polar rows

Let `H_jj′` be the relative blocks of the positive polar factor of a blocked direct sum,
and let `F_j` be the fixed-point tensor of a normalized positive semidefinite matrix `σ_j`.
Suppose that every relative block differs from its limit by at most `δ`. For `M ≥ 2`,
the overlaps `⟨φ_M(F_j), φ_M(H_jj′)⟩` differ from `δ_jj′` by at most
`C M δ² exp(C M δ²)` when `C M δ² < 1`. The constant precedes the arbitrary copy weights.

On the diagonal, the compression coefficient has a quadratic deficit by the column
normalization identity, and the idempotent power estimate applies. Off the diagonal,
the limiting mixed transfer is zero. Its `M`-th power has norm of order `δ^M`, which is
quadratic for `M ≥ 2`; the smallness condition already supplies the needed contraction.
No quadratic absolute-trace estimate for `M = 1` is asserted.

This is a project refinement of arXiv:2307.01696, Supplemental Material, Lemma 1′(ii),
eq. `eq:fid_err_gen_non_normal`. It does not assert a quadratic norm estimate for the
positive polar factor itself.

**Local fix (corrected multiplicity state):** the relative blocks use the rank-one copy
isometries of the corrected positive-factor decomposition in place of the diagonal copy
form of eq. (S5). See `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

**Local fix (mixed-transfer rate):** applying this estimate at the spectral rate requires
bounds on the mixed transfer spectra of distinct blocks as well as the diagonal spectra.
See `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.
-/

noncomputable section
namespace MPSTensor
open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
variable {d D b : ℕ} {m Dj : Fin b → ℕ}
    {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

/-- The diagonal relative-row overlap is quadratic for at least two blocks. -/
private theorem exists_norm_diagonal_relative_overlap_sub_one_le_sq
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' →
      ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (σ : (k : Fin b) → Matrix (Fin (Dj k)) (Fin (Dj k)) ℂ) (j : Fin b)
    (hσ : (σ j).PosSemidef) (htr : (σ j).trace = 1)
    (hfix : Kraus.transferMap (Aj j) (σ j) = σ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : CopyWeights b m) (q : ℕ), q ≠ 0 → ∀ (δ : ℝ) (M : ℕ),
      2 ≤ M →
      (∀ k, ‖relativeRow (repeatedBlockSum Aj ι μ) ι μ q k j -
        relativeRowLimit ι μ q σ k j‖ ≤ δ) → C * (M * δ ^ 2) < 1 →
      ‖mpvOverlap (ofPhysicalMatrixLM
          (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j))
          (fixedPointTensor (σ j)) M - 1‖ ≤
        C * (M * δ ^ 2) * Real.exp (C * (M * δ ^ 2)) := by
  classical
  have : NeZero (Dj j) := Matrix.neZero_of_trace_eq_one htr
  let F := fixedPointTensor (σ j)
  let Pinf := (CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)
  have hFinf : ofPhysicalMatrixLM Pinf = F := ofPhysicalMatrix_sqrt_transpose_kronecker_one _
  let Ψ := mixedTransferMatrixLeft F
  let R := transferMatrix (Kraus.mixedMapLM F F)
  have hPsiInf : Ψ Pinf = R := by
    change transferMatrix (Kraus.mixedMapLM (ofPhysicalMatrixLM Pinf) F) = _
    rw [hFinf]
  have hRi : IsIdempotentElem R := isIdempotentElem_transferMatrix_fixedPointTensor hσ htr
  have hRtr : Matrix.traceLinearMap (Fin (Dj j) × Fin (Dj j)) ℂ ℂ R = 1 := by
    rw [← pow_one R]
    change (transferMatrix (Kraus.mixedMapLM F F) ^ 1).trace = 1
    rw [trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap]
    exact mpvOverlap_fixedPointTensor_self hσ htr 1
  let trL := LinearMap.toContinuousLinearMap
    (Matrix.traceLinearMap (Fin (Dj j) × Fin (Dj j)) ℂ ℂ)
  obtain ⟨C0, hC0, hgen⟩ := IsIdempotentElem.exists_norm_trace_pow_sub_one_le_sq hRi
    (tr := Matrix.traceLinearMap (Fin (Dj j) × Fin (Dj j)) ℂ ℂ)
    (fun A B => Matrix.trace_mul_comm A B) (norm_nonneg _) trL.le_opNorm hRtr
  obtain ⟨Ca, hCa, hdef⟩ := exists_relative_diagonal_deficit_le hι hdisj σ j hσ htr hfix
  let Kt := ‖LinearMap.toContinuousLinearMap Ψ‖
  let t := Kt + Ca + 1
  have ht0 : 0 < t := by dsimp only [t]; positivity
  have htKt : Kt ≤ t := by dsimp only [t]; linarith
  have htCa : Ca ≤ t ^ 2 := by
    dsimp only [t]
    nlinarith [norm_nonneg (LinearMap.toContinuousLinearMap Ψ), sq_nonneg Ca]
  let C := C0 * t ^ 2 + 1
  refine ⟨C, by dsimp only [C]; positivity, fun μ q hq δ M hM hrow hsmall => ?_⟩
  let H := relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j
  let α := (Kraus.mixedMapLM (ofPhysicalMatrixLM H) F (σ j)).trace
  have hα0 : 0 ≤ α := relative_diagonal_nonneg hι hdisj μ q j hσ
  obtain ⟨ha, hdeficit⟩ := hdef μ q hq δ hrow
  change ‖α‖ ≤ 1 at ha
  change ‖1 - α‖ ≤ Ca * δ ^ 2 at hdeficit
  have hcoef : α = (α.re : ℂ) := by
    have hnorm : α.re = ‖α‖ := by
      simpa using congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hα0)
    rw [hnorm]
    exact Complex.eq_coe_norm_of_nonneg hα0
  have hre : α.re ≤ 1 := (Complex.re_le_norm α).trans ha
  have hαsq : 1 - α.re ≤ (t * δ) ^ 2 := by
    calc
      _ = (1 - α).re := by simp
      _ ≤ ‖1 - α‖ := Complex.re_le_norm _
      _ ≤ Ca * δ ^ 2 := hdeficit
      _ ≤ t ^ 2 * δ ^ 2 := mul_le_mul_of_nonneg_right htCa (sq_nonneg δ)
      _ = _ := (mul_pow _ _ _).symm
  have hcomp : R * Ψ H * R = (α.re : ℂ) • R := by
    rw [← hcoef]
    exact transferMatrix_fixedPointTensor_mul_mul hσ (ofPhysicalMatrixLM H) F
  have hHd : ‖H - Pinf‖ ≤ δ := by
    have h := hrow j
    rw [relativeRowLimit_self hι hdisj] at h
    exact h
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hHd
  have hT : ‖Ψ H - R‖ ≤ t * δ := by
    rw [← hPsiInf, ← map_sub]
    exact ((LinearMap.toContinuousLinearMap Ψ).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left hHd (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right htKt hδ0))
  have hsmall' : C0 * (M * (t * δ) ^ 2) < 1 := by
    have hcoeff : C0 * t ^ 2 ≤ C := by dsimp only [C]; linarith
    calc
      _ = (C0 * t ^ 2) * (M * δ ^ 2) := by ring
      _ ≤ C * (M * δ ^ 2) := mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ < 1 := hsmall
  have h := hgen (Ψ H) α.re (t * δ) M hM hcomp hT hre hαsq hsmall'
  have hover : Matrix.traceLinearMap (Fin (Dj j) × Fin (Dj j)) ℂ ℂ ((Ψ H) ^ M) =
      mpvOverlap (ofPhysicalMatrixLM H) F M :=
    trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap _ _ M
  rw [hover] at h
  refine h.trans ?_
  have hcoeff : C0 * t ^ 2 ≤ C := by dsimp only [C]; linarith
  calc
    _ = (C0 * t ^ 2) * (M * δ ^ 2) *
        Real.exp ((C0 * t ^ 2) * (M * δ ^ 2)) := by
      have hy : C0 * (M * (t * δ) ^ 2) = (C0 * t ^ 2) * (M * δ ^ 2) := by ring
      rw [hy]
    _ ≤ C * (M * δ ^ 2) * Real.exp (C * (M * δ ^ 2)) := by gcongr

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-- A row with zero limiting transfer has a quadratic overlap once two factors occur. -/
private theorem exists_norm_zero_row_overlap_le_sq {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (F : MPSTensor (D₂ * D₂) D₂) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : Matrix (Fin D₂ × Fin D₂) (Fin D₁ × Fin D₁) ℂ) (δ : ℝ) (M : ℕ),
      ‖G‖ ≤ δ → 2 ≤ M → C * (M * δ ^ 2) < 1 →
      ‖mpvOverlap (ofPhysicalMatrixLM G) F M‖ ≤
        C * (M * δ ^ 2) * Real.exp (C * (M * δ ^ 2)) := by
  let Φ : Module.End ℂ (Matrix (Fin D₁) (Fin D₂) ℂ) ≃ₐ[ℂ] _ :=
    Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ)
  let Ψ : Matrix (Fin D₂ × Fin D₂) (Fin D₁ × Fin D₁) ℂ →ₗ[ℂ]
      (Matrix (Fin D₁) (Fin D₂) ℂ →L[ℂ] Matrix (Fin D₁) (Fin D₂) ℂ) :=
    Φ.toLinearMap ∘ₗ mixedMapLMLeft (D₁ := D₁) F ∘ₗ ofPhysicalMatrixLM
  let tr : (Matrix (Fin D₁) (Fin D₂) ℂ →L[ℂ] Matrix (Fin D₁) (Fin D₂) ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.trace ℂ (Matrix (Fin D₁) (Fin D₂) ℂ) ∘ₗ Φ.symm.toLinearMap
  let Kt := ‖LinearMap.toContinuousLinearMap Ψ‖
  let Kr := ‖LinearMap.toContinuousLinearMap tr‖
  have hKt : 0 ≤ Kt := norm_nonneg _
  have hKr : 0 ≤ Kr := norm_nonneg _
  let C := Kr * Kt ^ 2 + Kt ^ 2 + 1
  have hC0 : 0 < C := by dsimp only [C]; positivity
  have hCkt : Kt ^ 2 ≤ C := by dsimp only [C]; nlinarith [sq_nonneg Kt]
  have hCkr : Kr * Kt ^ 2 ≤ C := by dsimp only [C]; nlinarith [sq_nonneg Kt]
  refine ⟨C, hC0, fun G δ M hG hM hsmall => ?_⟩
  have hδ0 : 0 ≤ δ := (norm_nonneg G).trans hG
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hT : ‖Ψ G‖ ≤ Kt * δ := ((LinearMap.toContinuousLinearMap Ψ).le_opNorm G).trans
    (mul_le_mul_of_nonneg_left hG hKt)
  have hbase0 : 0 ≤ Kt * δ := mul_nonneg hKt hδ0
  have hbase1 : Kt * δ ≤ 1 := by
    have hsq : (Kt * δ) ^ 2 ≤ C * (M * δ ^ 2) := by
      calc
        _ = Kt ^ 2 * δ ^ 2 := mul_pow _ _ _
        _ ≤ C * δ ^ 2 := mul_le_mul_of_nonneg_right hCkt (sq_nonneg δ)
        _ ≤ C * (M * δ ^ 2) := by
          gcongr
          exact le_mul_of_one_le_left (sq_nonneg δ) hM1
    nlinarith
  have hpower : ‖(Ψ G) ^ M‖ ≤ Kt ^ 2 * δ ^ 2 := by
    calc
      _ ≤ ‖Ψ G‖ ^ M := norm_pow_le _ _
      _ ≤ (Kt * δ) ^ M := pow_le_pow_left₀ (norm_nonneg _) hT M
      _ ≤ (Kt * δ) ^ 2 := pow_le_pow_of_le_one hbase0 hbase1 hM
      _ = _ := mul_pow _ _ _
  have hover : tr ((Ψ G) ^ M) = mpvOverlap (ofPhysicalMatrixLM G) F M := by
    change LinearMap.trace ℂ (Matrix (Fin D₁) (Fin D₂) ℂ)
      (Φ.symm ((Φ (Kraus.mixedMapLM (ofPhysicalMatrixLM G) F)) ^ M)) = _
    rw [← map_pow, AlgEquiv.symm_apply_apply]
    exact trace_mixedMapLM_rect_pow_eq_mpvOverlap _ _ M
  rw [← hover]
  calc
    _ ≤ Kr * ‖(Ψ G) ^ M‖ := (LinearMap.toContinuousLinearMap tr).le_opNorm _
    _ ≤ Kr * (Kt ^ 2 * δ ^ 2) := mul_le_mul_of_nonneg_left hpower hKr
    _ ≤ C * (M * δ ^ 2) := by
      calc
        _ = (Kr * Kt ^ 2) * δ ^ 2 := by ring
        _ ≤ C * δ ^ 2 := mul_le_mul_of_nonneg_right hCkr (sq_nonneg δ)
        _ ≤ C * (M * δ ^ 2) := by
          gcongr
          exact le_mul_of_one_le_left (sq_nonneg δ) hM1
    _ ≤ C * (M * δ ^ 2) * Real.exp (C * (M * δ ^ 2)) := by
      exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))

/-- All actual relative-row overlaps are quadratic for at least two blocks, with a constant
chosen before the arbitrary nonzero copy weights.

Project refinement of arXiv:2307.01696, Supplemental Material, Lemma 1′(ii),
eq. `eq:fid_err_gen_non_normal`, using the corrected multiplicity block form. -/
theorem exists_norm_relative_row_overlap_sub_ite_le_sq
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' →
      ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (σ : (k : Fin b) → Matrix (Fin (Dj k)) (Fin (Dj k)) ℂ)
    (hσ : ∀ k, (σ k).PosSemidef) (htr : ∀ k, (σ k).trace = 1)
    (hfix : ∀ k, Kraus.transferMap (Aj k) (σ k) = σ k) (j j' : Fin b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : CopyWeights b m) (q : ℕ), q ≠ 0 → ∀ (δ : ℝ) (M : ℕ),
      2 ≤ M →
      (∀ k l, ‖relativeRow (repeatedBlockSum Aj ι μ) ι μ q k l -
        relativeRowLimit ι μ q σ k l‖ ≤ δ) → C * (M * δ ^ 2) < 1 →
      ‖mpvOverlap (ofPhysicalMatrixLM
          (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j'))
          (fixedPointTensor (σ j)) M - (if j = j' then 1 else 0)‖ ≤
        C * (M * δ ^ 2) * Real.exp (C * (M * δ ^ 2)) := by
  classical
  by_cases hjj : j = j'
  · subst j'
    obtain ⟨C, hC, hgen⟩ := exists_norm_diagonal_relative_overlap_sub_one_le_sq hι hdisj
      σ j (hσ j) (htr j) (hfix j)
    refine ⟨C, hC, fun μ q hq δ M hM hrow hsmall => ?_⟩
    simpa only [ite_eq_left, ite_true] using hgen μ q hq δ M hM (fun k => hrow k j) hsmall
  · have : NeZero (Dj j) := Matrix.neZero_of_trace_eq_one (htr j)
    have : NeZero (Dj j') := Matrix.neZero_of_trace_eq_one (htr j')
    obtain ⟨C, hC, hgen⟩ := exists_norm_zero_row_overlap_le_sq (D₁ := Dj j')
      (fixedPointTensor (σ j))
    refine ⟨C, hC, fun μ q _ δ M hM hrow hsmall => ?_⟩
    have hG := hrow j j'
    rw [relativeRowLimit_of_ne hι hdisj μ q σ hjj, sub_zero] at hG
    simpa only [ite_eq_right hjj, sub_zero] using hgen _ δ M hG hM hsmall

end MPSTensor
