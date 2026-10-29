/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.TranslationInvariantUniqueness

/-!
# Explicit phase changes within the quadratic reconstruction system

Multiplying the tensor of a solution by a unit-modulus scalar preserves
system (S) after geometric scalar changes of the two gauge families. If
the scalar is an Nth root of unity, the actual length-N vector is unchanged.
This gives an actual rephased solution over the same supplied OBC window.

Source: PGVWC07, arXiv:quant-ph/0608197, system (S) and Theorem 8,
lines 1139--1176. The finite-ring phase correction is documented in
`docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex`.
-/

open scoped BigOperators Matrix Kronecker

namespace MPSTensor.QuadraticReconstructionSolution

variable {d D m : ℕ}
    {H : Fin m → Fin d → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}

/-- Rephase a solution's tensor by a unit-modulus scalar, with
Yhat_j = ξ^(-j) Y_j and Zhat_j = ξ^(j+1) Z_j. All equations of the same
quadratic system are retained. Source: PGVWC07, system (S), lines 1139--1152,
and the correction in docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex. -/
noncomputable def rephase (s : QuadraticReconstructionSolution H)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) : QuadraticReconstructionSolution H where
  leftGauge j := (ξ⁻¹) ^ j.val • s.leftGauge j
  rightGauge j := ξ ^ (j.val + 1) • s.rightGauge j
  tensor i := ξ • s.tensor i
  kronecker_eq i j := by
    have hξ0 : ξ ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hξ
      exact zero_ne_one hξ
    have hratio : (ξ⁻¹) ^ j.val * ξ ^ (j.val + 1) = ξ := by
      rw [pow_succ, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero j.val hξ0)]
    rw [Matrix.smul_kronecker, s.kronecker_eq]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hratio]
  leftGauge_mul_rightGauge j hj := by
    have hξ0 : ξ ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hξ
      exact zero_ne_one hξ
    change ((ξ⁻¹) ^ (j.val + 1) • s.leftGauge ⟨j.val + 1, hj⟩) *
      (ξ ^ (j.val + 1) • s.rightGauge j) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, s.leftGauge_mul_rightGauge j hj,
      ← mul_pow, inv_mul_cancel₀ hξ0, one_pow, one_smul]
  sum_mul_conjTranspose := by
    have hstar : star ξ * ξ = 1 := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ]
      norm_num
    rw [sum_smul_mul_conjTranspose_smul, s.sum_mul_conjTranspose, hstar, one_smul]

/-- The tensor component of the explicit rephased solution.
Source: the scalar correction of PGVWC07 Theorem 8. -/
@[simp] theorem rephase_tensor (s : QuadraticReconstructionSolution H)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) : (s.rephase ξ hξ).tensor = fun i ↦ ξ • s.tensor i := rfl

/-- An Nth-root rephasing preserves the actual length-N state of the
solution. Source: the corrected finite-ring conclusion of PGVWC07 Theorem 8,
docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex. -/
theorem mpv_rephase (s : QuadraticReconstructionSolution H) (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {N : ℕ} (hξN : ξ ^ N = 1) (σ : Fin N → Fin d) :
    mpv (s.rephase ξ hξ).tensor σ = mpv s.tensor σ := by
  rw [rephase_tensor, mpv_smul, hξN, one_mul]

end MPSTensor.QuadraticReconstructionSolution
