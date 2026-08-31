/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Analytic bounds for Nachtergaele's martingale summation

This file records the two elementary estimates used in the proof of
Nachtergaele's Theorem 2.1(i) (cond-mat/9410110, lines 1195--1259). The first is
the real-part form of the weighted estimate applied twice in display `Enpsi2`.
The second turns C3 into its pointwise norm-square form. These are the analytic
inputs to the source's choices
\(c_1 = 1 - \epsilon_l\sqrt{l+1}\) and
\(c_2 = \epsilon_l/\sqrt{l+1}\), which yield the exact factor
\(\frac{\gamma_{l+1}}{d_{l+1}}(1-\epsilon_l\sqrt{l+1})^2\).
-/

open scoped InnerProductSpace

namespace FrustrationFree

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The real-part form of the weighted inner-product estimate used twice in
Nachtergaele's display `Enpsi2` (cond-mat/9410110, lines 1223--1239). -/
theorem re_inner_le_weighted_norm_sq (x y : E) {c : ℝ} (hc : 0 < c) :
    (⟪x, y⟫_ℂ).re ≤ (1 / (2 * c)) * ‖x‖ ^ 2 + (c / 2) * ‖y‖ ^ 2 := by
  calc
    (⟪x, y⟫_ℂ).re ≤ ‖x‖ * ‖y‖ := re_inner_le_norm (𝕜 := ℂ) x y
    _ = (1 / 2 : ℝ) * (2 * ‖y‖ * ‖x‖) := by ring
    _ ≤ (1 / 2 : ℝ) * (c * ‖y‖ ^ 2 + c⁻¹ * ‖x‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (two_mul_le_add_mul_sq hc) (by positivity)
    _ = (1 / (2 * c)) * ‖x‖ ^ 2 + (c / 2) * ‖y‖ ^ 2 := by
      field_simp [hc.ne']
      ring

/-- If \(P\) is an orthogonal projection and the literal composition \(QP\)
has operator norm at most \(\varepsilon\), then its value on the range of \(P\) has the C3
norm-square bound used in cond-mat/9410110, lines 1240--1249, from condition C3
at lines 1083--1094. No strict positivity of \(\varepsilon\) is required; the operator-norm
hypothesis already implies its nonnegativity. -/
theorem norm_sq_apply_projection_le_of_norm_comp_le
    (Q : E →L[ℂ] F) (P : E →L[ℂ] E)
    (hP : P.toLinearMap.IsSymmetricProjection) {ε : ℝ}
    (hQP : ‖Q.comp P‖ ≤ ε) (v : E) :
    ‖Q (P v)‖ ^ 2 ≤ ε ^ 2 * ‖P v‖ ^ 2 := by
  have hPP : P (P v) = P v := by
    have h := congrArg (fun T : E →ₗ[ℂ] E ↦ T v) hP.isIdempotentElem.eq
    simpa [Module.End.mul_apply] using h
  have hnorm : ‖Q (P v)‖ ≤ ε * ‖P v‖ := by
    calc
      ‖Q (P v)‖ = ‖(Q.comp P) (P v)‖ := by simp [hPP]
      _ ≤ ‖Q.comp P‖ * ‖P v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖P v‖ := mul_le_mul_of_nonneg_right hQP (norm_nonneg _)
  simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg (Q (P v))) hnorm 2

end FrustrationFree
