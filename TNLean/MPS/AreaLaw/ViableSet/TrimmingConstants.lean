/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Numerical estimates for the trimmed witness

These auxiliary real-variable estimates concern the constant `c = (Δ / 169)²` of Landau,
Vazirani and Vidick, arXiv:1307.5143v1, `References/1307.5143/algo53.tex`, equation
`eq:def-ce`, lines 290–293, and the energy bound in Lemma `l:within`, lines 509–515.
They do not assert the existence of a trimmed witness.
-/

namespace TNLean.MPS.AreaLaw

/-- An auxiliary numerical estimate for the trimming energy in LVV13, Lemma `l:within`
(`References/1307.5143/algo53.tex`, lines 509–515): an input energy excess `8c` and overlap
loss `4c` give an energy excess at most `6√c` when `0 ≤ c ≤ 1/1600`. -/
theorem trimming_energy_fraction_le_six_mul_sqrt {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ 1 / 1600) :
    (8 * c + 4 * √(2 * c)) / (1 - 8 * c) ≤ 6 * √c := by
  have hden : 0 < 1 - 8 * c := by linarith
  have hr0 := Real.sqrt_nonneg c
  have hrsq := Real.sq_sqrt hc0
  have hr : √c ≤ 1 / 40 := by nlinarith
  have hs : √(2 * c) ≤ 17 / 12 * √c := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨mul_nonneg (by norm_num) hr0, by nlinarith⟩
  have hcr : 8 * c ≤ 1 / 5 * √c := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr)]
  have hdenr : 597 / 100 * √c ≤ 6 * √c * (1 - 8 * c) := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hc)]
  apply (div_le_iff₀ hden).mpr
  calc
    8 * c + 4 * √(2 * c) ≤ 88 / 15 * √c := by linarith
    _ ≤ 597 / 100 * √c := mul_le_mul_of_nonneg_right (by norm_num) hr0
    _ ≤ 6 * √c * (1 - 8 * c) := hdenr

/-- The three inequalities of LVV13, equation `eq:def-ce`
(`References/1307.5143/algo53.tex`, lines 290–293), together with positivity and the bound
`c ≤ 1/1600`, for `c = (Δ / 169)²` and `0 < Δ ≤ 4`. -/
theorem lvv_trimming_constant_bounds {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 4) :
    0 < (Δ / 169) ^ 2 ∧ (Δ / 169) ^ 2 ≤ 1 / 1600 ∧
      (Δ / 169) ^ 2 * (1 + 1 / Δ) ≤ 1 / 2 ∧
      14 * √((Δ / 169) ^ 2) / Δ < 1 / 12 ∧
      84 * (Δ / 169) ^ 2 / Δ < 1 / 2 := by
  have hΔsq : Δ ^ 2 ≤ 16 := by
    nlinarith [mul_nonneg hΔ0.le (sub_nonneg.mpr hΔ4)]
  have hsmall : (Δ / 169) ^ 2 ≤ 1 / 1600 := by nlinarith
  have hratio : (Δ / 169) ^ 2 / Δ = Δ / 28561 := by
    apply (div_eq_iff hΔ0.ne').mpr
    ring
  have hsqrt : √((Δ / 169) ^ 2) = Δ / 169 :=
    Real.sqrt_sq (div_nonneg hΔ0.le (by norm_num))
  refine ⟨pow_pos (div_pos hΔ0 (by norm_num)) 2, hsmall, ?_, ?_, ?_⟩
  · rw [mul_add, mul_one, mul_one_div, hratio]
    nlinarith
  · rw [hsqrt]
    apply (div_lt_iff₀ hΔ0).mpr
    linarith
  · rw [show 84 * (Δ / 169) ^ 2 / Δ = 84 * ((Δ / 169) ^ 2 / Δ) by ring, hratio]
    linarith

/-- Auxiliary energy estimates at LVV13's constant, for Lemma `l:within`
(`References/1307.5143/algo53.tex`, lines 509–515). These are numerical inequalities,
without an assertion about chain states. -/
theorem lvv_trimming_energy_bounds {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 4) :
    (8 * (Δ / 169) ^ 2 + 4 * √(2 * (Δ / 169) ^ 2)) / (1 - 8 * (Δ / 169) ^ 2) ≤
        6 * √((Δ / 169) ^ 2) ∧
      6 * √((Δ / 169) ^ 2) ≤ Δ / 12 := by
  obtain ⟨hc0, hc, -⟩ := lvv_trimming_constant_bounds hΔ0 hΔ4
  refine ⟨trimming_energy_fraction_le_six_mul_sqrt hc0.le hc, ?_⟩
  rw [Real.sqrt_sq (div_nonneg hΔ0.le (by norm_num))]
  linarith

end TNLean.MPS.AreaLaw
