/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.SpectralWindowPrecision
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Scalar budgets for physical soft clusters

A bound on the crossing bonds gives residual budgets independent of the
selected soft ground energy. A uniform norm ceiling then fixes the precision
of a Hermitian approximation before its actual spectral windows are known.
These are numerical auxiliaries for ALVV, arXiv:1602.08828v2,
`t:aisefficient`, lines 1373–1420. The residual and perturbation estimates
retain the corrections in `docs/paper-gaps/alvv16_soft_regional_residuals.tex`
and `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

namespace TNLean.MPS.AreaLaw.ALVV

private theorem residual_budget_mono {C U V T t : ℝ} {m : ℕ}
    (hC4 : C ≤ 4) (hUV : U ≤ V) :
    3 * (8 * C * Real.exp (-(T - U) / 8) + (t / (m : ℝ)) * (T / t) ^ m) ≤
      3 * (32 * Real.exp (-(T - V) / 8) + (t / (m : ℝ)) * (T / t) ^ m) := by
  gcongr
  · linarith only [hC4]

/-- Coarse residual conditions imply the actual forward and reverse budgets,
without dependence on the selected soft ground energy. Numerical auxiliary
to ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1420. -/
theorem soft_cluster_scalar_residual_budgets {C E mu g T0 T1 t tau : ℝ} {m : ℕ}
    (hC4 : C ≤ 4) (hEC : E ≤ C) (hmu : -30 ≤ mu) (hg : 0 < g)
    (hT0 : g / 40 + 24 ≤ T0) (ht : 156 + 2 * g ≤ t)
    (hT1 : 156 + 2 * g ≤ T1)
    (hO : 3 * (32 * Real.exp (-(T0 - g / 40 - 24) / 8) +
      (t / (m : ℝ)) * (T0 / t) ^ m) ≤ tau * g / 1000000)
    (hR : 3 * (32 * Real.exp (-(T1 - 156 - 2 * g) / 8) +
      (t / (m : ℝ)) * (T1 / t) ^ m) ≤ tau * g / 1000000) :
    let U := 2 * (E - mu + 19 * g / 20 + 30 + 3 * C + 2)
    g / 40 + 3 * C + 12 ≤ T0 ∧ U ≤ t ∧ U ≤ T1 ∧
      3 * (8 * C * Real.exp (-(T0 - g / 40 - 3 * C - 12) / 8) +
        (t / (m : ℝ)) * (T0 / t) ^ m) ≤ tau * g / 1000000 ∧
      3 * (8 * C * Real.exp (-(T1 - U) / 8) +
        (t / (m : ℝ)) * (T1 / t) ^ m) ≤ tau * g / 1000000 := by
  intro U
  have hU : U ≤ 156 + 2 * g := by
    dsimp only [U]
    linarith only [hEC, hmu, hC4, hg]
  refine ⟨by linarith only [hC4, hT0], hU.trans ht, hU.trans hT1, ?_, ?_⟩
  · refine le_trans ?_ hO
    simpa only [sub_add_eq_sub_sub] using
      (residual_budget_mono (T := T0) (t := t) (m := m)
        (U := g / 40 + 3 * C + 12) (V := g / 40 + 24) hC4
        (by linarith only [hC4]))
  · refine le_trans ?_ hR
    simpa only [sub_add_eq_sub_sub] using
      (residual_budget_mono (T := T1) (t := t) (m := m)
        (U := U) (V := 156 + 2 * g) hC4 hU)

/-- One explicit precision controls both literal spectral-window counts,
using only a norm ceiling and the original centered energy interval.
Numerical auxiliary to ALVV, arXiv:1602.08828v2, `t:aisefficient`,
lines 1412–1420, with the corrected finite-window comparison. -/
theorem soft_cluster_actual_window_losses {A M E g tau : ℝ}
    (hA : 0 ≤ A) (hAM : A ≤ M) (hE0 : 0 ≤ E) (hE4 : E ≤ 4)
    (hg : 0 < g) (htau : 0 < tau) :
    let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
    let V := A + xi
    let nLo := ⌈((E + g / 20) - min (E + g / 20 - 1) (-V)) / (2 * xi)⌉₊
    let nHi := ⌈((E + 3 * g / 4) - min (E + 3 * g / 4 - 1) (-V)) / (2 * xi)⌉₊
    0 < xi ∧ xi ≤ 1 ∧
      (nLo : ℝ) * (2 * xi) ^ 2 / (g / 5 + xi) ^ 2 ≤ tau / 400 ∧
      (nHi : ℝ) * (2 * xi) ^ 2 / (g / 5 + xi) ^ 2 ≤ tau / 400 := by
  intro xi V nLo nHi
  obtain ⟨hxi, hxi1, _hbudget, huniform⟩ :=
    Real.soft_cluster_window_precision_parameters (hA.trans hAM) hg htau
  refine ⟨hxi, hxi1, ?_, ?_⟩
  · exact (Real.finite_window_loss_le_envelope hA hAM
      (by positivity : 0 ≤ E + g / 20)
      (by linarith only [hE4, hg] : E + g / 20 ≤ 4 + g)
      hxi (by positivity : 0 < g / 5)).trans huniform
  · exact (Real.finite_window_loss_le_envelope hA hAM
      (by positivity : 0 ≤ E + 3 * g / 4)
      (by linarith only [hE4, hg] : E + 3 * g / 4 ≤ 4 + g)
      hxi (by positivity : 0 < g / 5)).trans huniform

end TNLean.MPS.AreaLaw.ALVV
