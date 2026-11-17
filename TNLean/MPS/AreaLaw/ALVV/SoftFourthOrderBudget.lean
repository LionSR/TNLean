/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The fourth-order soft truncation and the calibrated precision

The proof of ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1420, uses soft
truncation of fourth order. The calibration of the gapped soft family in
`UniformPhysicalSoftCalibration` instead fixes the residual budget `τ g / 10⁶` with
`τ = (D²⁴ M¹⁰)⁻¹`, where `D ≥ 1` is the family count and `M ≥ 3 t` the norm ceiling. At order
`m = 4` the remainder `(t / 4) (T₀ / t)⁴` decays only like `t⁻³`, while the budget decays at
least like `t⁻¹⁰`, so for every gap `g ≤ 10²⁰` no scale `t ≥ 12` and cutoff `T₀ ≥ 24` meet the
budget. The fourth-order choice is therefore not an instance of that calibration; recovering
it needs a different precision requirement. Numerical auxiliary; see
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`.
-/

namespace TNLean.MPS.AreaLaw.ALVV

/-- **The fourth order misses the calibrated residual budget.** With `m = 4`, `t ≥ 12`,
`T₀ ≥ 24`, `M ≥ 3 t`, `D ≥ 1`, `τ = (D²⁴ M¹⁰)⁻¹` and `0 < g ≤ 10²⁰`, the residual condition
`3 (32 e^{-(T₀ - g/40 - 24)/8} + (t/4)(T₀/t)⁴) ≤ τ g / 10⁶` of the calibrated gapped soft
family fails. Numerical auxiliary to ALVV, arXiv:1602.08828v2, `t:aisefficient`,
lines 1373–1420. -/
theorem not_soft_fourth_order_residual_budget {g t T0 M D : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 10 ^ 20) (ht : 12 ≤ t) (hT0 : 24 ≤ T0) (hM : 3 * t ≤ M)
    (hD : 1 ≤ D) :
    ¬ 3 * (32 * Real.exp (-(T0 - g / 40 - 24) / 8) + (t / (4 : ℕ)) * (T0 / t) ^ 4) ≤
      (1 / (D ^ 24 * M ^ 10)) * g / 1000000 := by
  intro hbudget
  have ht0 : 0 < t := by linarith
  have hM0 : 0 < M := by linarith
  push_cast at hbudget
  -- The remainder is at least `24⁴ / (4 t³)`.
  have hratio : 24 / t ≤ T0 / t := div_le_div_of_nonneg_right hT0 ht0.le
  have hpow : (24 / t) ^ 4 ≤ (T0 / t) ^ 4 := pow_le_pow_left₀ (by positivity) hratio 4
  have hrem : 82944 / t ^ 3 ≤ (t / 4) * (T0 / t) ^ 4 := by
    have h : (t / 4) * (24 / t) ^ 4 = 82944 / t ^ 3 := by
      field_simp
      ring
    rw [← h]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hexp : 0 ≤ 32 * Real.exp (-(T0 - g / 40 - 24) / 8) := by positivity
  -- The budget is at most `10¹⁴ / (3 t)¹⁰`.
  have hD24 : 1 ≤ D ^ 24 := one_le_pow₀ hD
  have hM10 : (3 * t) ^ 10 ≤ M ^ 10 := pow_le_pow_left₀ (by positivity) hM 10
  have hden : (3 * t) ^ 10 ≤ D ^ 24 * M ^ 10 := by nlinarith [pow_pos hM0 10]
  have h3t : 0 < (3 * t) ^ 10 := by positivity
  have hbud : (1 / (D ^ 24 * M ^ 10)) * g / 1000000 ≤ 10 ^ 14 / (3 * t) ^ 10 := by
    rw [div_le_div_iff₀ (by norm_num) h3t]
    have hinv : 1 / (D ^ 24 * M ^ 10) ≤ 1 / (3 * t) ^ 10 :=
      one_div_le_one_div_of_le h3t hden
    have : (1 / (D ^ 24 * M ^ 10)) * g ≤ (1 / (3 * t) ^ 10) * 10 ^ 20 :=
      mul_le_mul hinv hg1 hg.le (by positivity)
    calc (1 / (D ^ 24 * M ^ 10)) * g * (3 * t) ^ 10
        ≤ (1 / (3 * t) ^ 10) * 10 ^ 20 * (3 * t) ^ 10 :=
          mul_le_mul_of_nonneg_right this h3t.le
      _ = 10 ^ 14 * 1000000 := by field_simp; norm_num
  -- Combine: `3 · 82944 / t³ ≤ 10¹⁴ / (3 t)¹⁰` contradicts `t ≥ 12`.
  have hkey : 3 * (82944 / t ^ 3) ≤ 10 ^ 14 / (3 * t) ^ 10 := by linarith
  have ht3 : 0 < t ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hkey h3t.le
  rw [div_mul_cancel₀ _ h3t.ne'] at hmul
  have h7 : (12 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht 7
  have hexpand : 3 * (82944 / t ^ 3) * (3 * t) ^ 10 = 248832 * 59049 * t ^ 7 := by
    field_simp
    ring
  rw [hexpand] at hmul
  nlinarith

end TNLean.MPS.AreaLaw.ALVV
