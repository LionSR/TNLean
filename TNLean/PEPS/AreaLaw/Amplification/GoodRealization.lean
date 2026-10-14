/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Choosing the scales and a good clock realization

In the proof of the amplification proposition the clocks run for the time
`t_* = C (𝓘 + w + K log n)` and the products are truncated at the radius
`r = ⌈(C' (t_* + K log n))^(1/α)⌉`. On one clock space three averaged
estimates hold: the excited component has expected squared norm at most
`M₀² e^{-g t_*}`, the omitted events contribute at most
`C t_* |S₀| M₀ e^{v t_* - c r^α}` in expectation, and the radius truncation
contributes at most `C t_* |S₀| (1 + r)² M₀ e^{-c r^α}`, where
`M₀ = exp ((𝓘 + 3w)/2)`.

This module takes `C = 6 / g`, chooses `C'` from `g`, `v` and `c`, and shows
that at all large `n` the three averages are at most `n^{-6K}`, `n^{-3K}` and
`n^{-3K}`. Markov's inequality and a union bound then select one realization on
which all three quantities are at most `n^{-K}`, which is
`eq:amplification-good-trajectory`.

The three random quantities are arbitrary real functions on an arbitrary
probability space, subject only to the averaged estimates; in the application
they are the norms `‖D (I - P_Ω) ζ‖`, `‖(D - D_ret) ζ‖` and `M₀ ‖D_ret - L'‖`.
The averaged estimates themselves, which come from the excited-state decay and
the local-products lemma, are inputs here.

## Main statements

* `exists_le_of_integral_sq_le_of_integral_le`: Markov's inequality and the
  union bound for the three failure events.
* `amplification_scale_bounds`: the choice of the time and radius makes the three
  averaged bounds at most `n^{-6K}`, `n^{-3K}` and `n^{-3K}`.
* `exists_good_realization`: `eq:amplification-good-trajectory`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `09-amplification.tex`, lines 453–499, equations
  `eq:amplification-time-choice` and `eq:amplification-good-trajectory`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open MeasureTheory Real

namespace TNLean.PEPS.AreaLaw

universe u

/-- **Markov's inequality and a union bound for three failure events.** On a
probability space, let `X ^ 2`, `Y` and `Z` be integrable with `Y, Z ≥ 0` almost
everywhere, and with expectations at most `a`, `b` and `c`. If
`a / ε² + b / ε + c / ε < 1`, then some realization has `X, Y, Z ≤ ε`.
Source: `09-amplification.tex`, lines 491–499. -/
theorem exists_le_of_integral_sq_le_of_integral_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y Z : Ω → ℝ} {a b c ε : ℝ} (hε : 0 < ε)
    (hXi : Integrable (fun ω ↦ X ω ^ 2) μ) (hY0 : 0 ≤ᵐ[μ] Y) (hYi : Integrable Y μ)
    (hZ0 : 0 ≤ᵐ[μ] Z) (hZi : Integrable Z μ)
    (ha : ∫ ω, X ω ^ 2 ∂μ ≤ a) (hb : ∫ ω, Y ω ∂μ ≤ b) (hc : ∫ ω, Z ω ∂μ ≤ c)
    (hsum : a / ε ^ 2 + b / ε + c / ε < 1) :
    ∃ ω, X ω ≤ ε ∧ Y ω ≤ ε ∧ Z ω ≤ ε := by
  by_contra h
  push Not at h
  have hcover : (Set.univ : Set Ω) ⊆
      ({ω | ε ^ 2 ≤ X ω ^ 2} ∪ {ω | ε ≤ Y ω}) ∪ {ω | ε ≤ Z ω} := by
    intro ω _
    by_cases hX : X ω ≤ ε
    · by_cases hY : Y ω ≤ ε
      · exact Or.inr (h ω hX hY).le
      · exact Or.inl (Or.inr (not_le.mp hY).le)
    · exact Or.inl (Or.inl (pow_le_pow_left₀ hε.le (not_le.mp hX).le 2))
  have h1 : (1 : ℝ) ≤ μ.real {ω | ε ^ 2 ≤ X ω ^ 2} + μ.real {ω | ε ≤ Y ω} +
      μ.real {ω | ε ≤ Z ω} :=
    calc (1 : ℝ) = μ.real Set.univ := probReal_univ.symm
      _ ≤ μ.real (({ω | ε ^ 2 ≤ X ω ^ 2} ∪ {ω | ε ≤ Y ω}) ∪ {ω | ε ≤ Z ω}) :=
        measureReal_mono hcover
      _ ≤ _ := (measureReal_union_le _ _).trans
        (add_le_add_left (measureReal_union_le _ _) _)
  have hε2 : 0 < ε ^ 2 := by positivity
  have pX : μ.real {ω | ε ^ 2 ≤ X ω ^ 2} ≤ a / ε ^ 2 := by
    rw [le_div_iff₀ hε2, mul_comm]
    exact (mul_meas_ge_le_integral_of_nonneg
      (ae_of_all _ fun ω ↦ sq_nonneg (X ω)) hXi (ε ^ 2)).trans ha
  have pY : μ.real {ω | ε ≤ Y ω} ≤ b / ε := by
    rw [le_div_iff₀ hε, mul_comm]
    exact (mul_meas_ge_le_integral_of_nonneg hY0 hYi ε).trans hb
  have pZ : μ.real {ω | ε ≤ Z ω} ≤ c / ε := by
    rw [le_div_iff₀ hε, mul_comm]
    exact (mul_meas_ge_le_integral_of_nonneg hZ0 hZi ε).trans hc
  linarith only [h1, pX, pY, pZ, hsum]

/-- The clock time `t_* = C (𝓘 + w + K log n)` of `eq:amplification-time-choice`,
with the constant `C = 6 / g`, which gives `g t_* ≥ 𝓘 + 3w + 6K log n`.
Source: `09-amplification.tex`, lines 455–461 and 481. -/
noncomputable def amplificationTime (g I w : ℝ) (K n : ℕ) : ℝ :=
  6 / g * (I + w + K * Real.log n)

/-- The radius `r = ⌈(C' (t + K log n))^(1/α)⌉` of `eq:amplification-time-choice`.
Source: `09-amplification.tex`, lines 455–461. -/
noncomputable def amplificationRadius (C' α t : ℝ) (K n : ℕ) : ℕ :=
  ⌈(C' * (t + K * Real.log n)) ^ α⁻¹⌉₊

/-- A polynomial weight is dominated by a stretched exponential: some `B ≥ 1`
bounds `(1 + r)² e^{-c r^α}` for every `r ≥ 0`. -/
theorem exists_one_add_sq_mul_exp_neg_rpow_le {c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ r : ℝ, 0 ≤ r → (1 + r) ^ 2 * exp (-(c * r ^ α)) ≤ B := by
  set m : ℕ := ⌈2 / α⌉₊
  have hfac : 0 ≤ (m.factorial : ℝ) / c ^ m := by positivity
  refine ⟨4 + 4 * ((m.factorial : ℝ) / c ^ m), by linarith only [hfac], fun r hr ↦ ?_⟩
  have hy : 0 ≤ r ^ α := rpow_nonneg hr α
  rcases le_total r 1 with hr1 | hr1
  · have hexp : exp (-(c * r ^ α)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith only [hc, hy])
    have hsq : (1 + r) ^ 2 ≤ 4 := by nlinarith only [hr, hr1]
    calc (1 + r) ^ 2 * exp (-(c * r ^ α)) ≤ 4 * 1 :=
          mul_le_mul hsq hexp (exp_pos _).le (by norm_num)
      _ ≤ _ := by linarith only [hfac]
  · have hm : 2 ≤ α * m := by
      have := Nat.le_ceil (2 / α)
      rw [div_le_iff₀ hα] at this
      linarith only [this]
    have hpow : r ^ 2 ≤ (r ^ α) ^ m := by
      rw [← rpow_natCast (r ^ α) m, ← rpow_mul hr, ← rpow_natCast r 2]
      exact rpow_le_rpow_of_exponent_le hr1 (by exact_mod_cast hm)
    have hfact : (c * r ^ α) ^ m / m.factorial ≤ exp (c * r ^ α) :=
      pow_div_factorial_le_exp (x := c * r ^ α) (by positivity) m
    have hkey : (r ^ α) ^ m * exp (-(c * r ^ α)) ≤ (m.factorial : ℝ) / c ^ m := by
      rw [exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (exp_pos _) (by positivity)]
      rw [div_le_iff₀ (by positivity), mul_pow] at hfact
      linarith only [hfact]
    calc (1 + r) ^ 2 * exp (-(c * r ^ α)) ≤ (4 * (r ^ α) ^ m) * exp (-(c * r ^ α)) := by
          gcongr
          nlinarith only [hr1, hpow]
      _ = 4 * ((r ^ α) ^ m * exp (-(c * r ^ α))) := by ring
      _ ≤ 4 * ((m.factorial : ℝ) / c ^ m) := by linarith only [hkey]
      _ ≤ _ := by linarith only

/-- `n^{-jK}` written as an exponential. -/
private theorem inv_pow_pow_eq_exp {n : ℕ} (hn : 0 < n) (K j : ℕ) :
    ((n : ℝ) ^ K)⁻¹ ^ j = exp (-(j * (K * Real.log n))) := by
  rw [← exp_log (by exact_mod_cast hn : (0 : ℝ) < n), ← exp_nat_mul, ← exp_neg,
    ← exp_nat_mul, exp_log (by exact_mod_cast hn : (0 : ℝ) < n)]
  ring_nf

/-- The final comparison of the scales: a prefactor at most `n` times `n²` is
absorbed by `n^{-6K}`, leaving `n^{-3K}`. -/
private theorem prefactor_le {n : ℕ} (hn : 2 ≤ n) {K : ℕ} (hK : 1 ≤ K) {P : ℝ}
    (hPn : P ≤ n) :
    P * exp (2 * Real.log n) * exp (-(6 * (K * Real.log n))) ≤
      exp (-(3 * (K * Real.log n))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 ≤ Real.log n := log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  calc P * exp (2 * Real.log n) * exp (-(6 * (K * Real.log n)))
      ≤ exp (Real.log n) * exp (2 * Real.log n) * exp (-(6 * (K * Real.log n))) := by
        rw [exp_log hn0]; gcongr
    _ = exp (3 * Real.log n - 6 * (K * Real.log n)) := by
        rw [← exp_add, ← exp_add]; ring_nf
    _ ≤ _ := exp_le_exp.mpr (by nlinarith only [hL, hK'])

/-- **The choice of the time and radius** (`eq:amplification-time-choice`). Let
`g, c > 0` and `v, C, C₀ ≥ 0`, and let `α > 0` and `K ≥ 1`. There are `C' > 0`
and a threshold `N ≥ 2` such that for every `n ≥ N`, every `𝓘, w ≥ 0` and every
`|S₀| ≤ C₀ n²`, the time `t_* = (6 / g)(𝓘 + w + K log n)` and the radius
`r = ⌈(C' (t_* + K log n))^(1/α)⌉` give, with `M₀ = exp ((𝓘 + 3w)/2)`,
`M₀² e^{-g t_*} ≤ n^{-6K}`, `C t_* |S₀| M₀ e^{v t_* - c r^α} ≤ n^{-3K}` and
`C t_* |S₀| (1 + r)² M₀ e^{-c r^α} ≤ n^{-3K}`. All parameters are fixed before `C'`
and `N`; the proof takes `C' = (g / 2 + 2 v + 12) / c`, which involves only `g`, `v`
and `c`.
Source: `09-amplification.tex`, lines 455–461 and 480–489. -/
theorem amplification_scale_bounds {g v c C C₀ α : ℝ} (hg : 0 < g) (hv : 0 ≤ v)
    (hc : 0 < c) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hα : 0 < α) {K : ℕ} (hK : 1 ≤ K) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ I w : ℝ, 0 ≤ I → 0 ≤ w →
      ∀ S : ℕ, (S : ℝ) ≤ C₀ * (n : ℝ) ^ 2 →
      exp ((I + 3 * w) / 2) ^ 2 * exp (-(g * amplificationTime g I w K n)) ≤
          ((n : ℝ) ^ K)⁻¹ ^ 6 ∧
        C * amplificationTime g I w K n * S * exp ((I + 3 * w) / 2) *
            exp (v * amplificationTime g I w K n - c *
              (amplificationRadius C' α (amplificationTime g I w K n) K n : ℝ) ^ α) ≤
          ((n : ℝ) ^ K)⁻¹ ^ 3 ∧
        C * amplificationTime g I w K n * S *
            (1 + (amplificationRadius C' α (amplificationTime g I w K n) K n : ℝ)) ^ 2 *
            exp ((I + 3 * w) / 2) *
            exp (-(c * (amplificationRadius C' α (amplificationTime g I w K n) K n : ℝ) ^ α)) ≤
          ((n : ℝ) ^ K)⁻¹ ^ 3 := by
  obtain ⟨B, hB1, hB⟩ := exists_one_add_sq_mul_exp_neg_rpow_le (half_pos hc) hα
  refine ⟨(g / 2 + 2 * v + 12) / c, by positivity, max 2 ⌈C * C₀ * B⌉₊, le_max_left _ _, ?_⟩
  intro n hn I w hI hw S hS
  set L := Real.log n with hLdef
  set t := amplificationTime g I w K n with htdef
  set r : ℝ := (amplificationRadius ((g / 2 + 2 * v + 12) / c) α t K n : ℝ) with hrdef
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 ≤ L := log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hKL : 0 ≤ K * L := mul_nonneg hK0 hL
  have hgt : g * t = 6 * (I + w + K * L) := by
    simp only [htdef, amplificationTime, hLdef]; field_simp
  have ht : 0 ≤ t :=
    mul_nonneg (div_nonneg (by norm_num) hg.le) (by linarith only [hI, hw, hKL])
  -- The radius exceeds the scale `x = C' (t + K log n)`.
  set x := (g / 2 + 2 * v + 12) / c * (t + K * L) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hcx : c * x = (g / 2 + 2 * v + 12) * (t + K * L) := by
    simp only [hxdef]; field_simp
  have hrx : x ≤ r ^ α := by
    have hceil : x ^ α⁻¹ ≤ r := Nat.le_ceil _
    calc x = (x ^ α⁻¹) ^ α := (rpow_inv_rpow hx0 hα.ne').symm
      _ ≤ r ^ α := rpow_le_rpow (rpow_nonneg hx0 _) hceil hα.le
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  -- The prefactor bound `|S₀| ≤ C₀ n²` and `M₀ ≤ e^{g t / 4}`.
  have hSn : (S : ℝ) ≤ C₀ * exp (2 * L) := by
    rw [hLdef, show 2 * Real.log n = (2 : ℕ) * Real.log n by norm_num, exp_nat_mul,
      exp_log hn0]
    exact hS
  have hM : (I + 3 * w) / 2 ≤ g * t / 4 := by rw [hgt]; nlinarith only [hI, hw, hKL]
  have htexp : t * exp (-t) ≤ 1 := by
    rw [exp_neg, ← div_eq_mul_inv, div_le_one (exp_pos _)]
    linarith only [add_one_le_exp t]
  have hCB : C * C₀ * B ≤ n := by
    have := (Nat.le_ceil (C * C₀ * B)).trans
      (by exact_mod_cast (le_max_right _ _).trans hn : (⌈C * C₀ * B⌉₊ : ℝ) ≤ n)
    exact this
  have hCC : C * C₀ ≤ n := by
    have : C * C₀ ≤ C * C₀ * B := le_mul_of_one_le_right (by positivity) hB1
    linarith only [this, hCB]
  -- A common estimate for a prefactor `P t |S₀| e^{E}` with `E ≤ -t - 6K log n`.
  have hcommon : ∀ P E : ℝ, 0 ≤ P → C₀ * P ≤ n → E ≤ -t - 6 * (K * L) →
      P * t * S * exp E ≤ ((n : ℝ) ^ K)⁻¹ ^ 3 := by
    intro P E hP hPn hE
    rw [inv_pow_pow_eq_exp (by omega) K 3]
    have hPt : 0 ≤ P * t := mul_nonneg hP ht
    calc P * t * S * exp E ≤ P * t * (C₀ * exp (2 * L)) * exp (-t - 6 * (K * L)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hSn hPt) (exp_le_exp.mpr hE)
            (exp_pos _).le (mul_nonneg hPt (by positivity))
      _ = (C₀ * P) * exp (2 * L) * exp (-(6 * (K * L))) * (t * exp (-t)) := by
          rw [show -t - 6 * (K * L) = -t + -(6 * (K * L)) by ring, exp_add]; ring
      _ ≤ (C₀ * P) * exp (2 * L) * exp (-(6 * (K * L))) * 1 :=
          mul_le_mul_of_nonneg_left htexp (by have := mul_nonneg hC₀ hP; positivity)
      _ ≤ _ := by rw [mul_one]; exact prefactor_le hn2 hK hPn
  have hcr : (g / 2 + 2 * v + 12) * (t + K * L) ≤ c * r ^ α := by
    rw [← hcx]; exact mul_le_mul_of_nonneg_left hrx hc.le
  have hgt0 : 0 ≤ g * t := mul_nonneg hg.le ht
  have hvt : 0 ≤ v * t := mul_nonneg hv ht
  have hgKL : 0 ≤ g * (K * L) := mul_nonneg hg.le hKL
  have hvKL : 0 ≤ v * (K * L) := mul_nonneg hv hKL
  refine ⟨?_, ?_, ?_⟩
  · rw [inv_pow_pow_eq_exp (by omega) K 6, sq, ← exp_add, ← exp_add, hgt]
    refine exp_le_exp.mpr ?_
    push_cast
    linarith only [hI, hw]
  · calc C * t * S * exp ((I + 3 * w) / 2) * exp (v * t - c * r ^ α)
        = C * t * S * exp ((I + 3 * w) / 2 + (v * t - c * r ^ α)) := by
          rw [exp_add]; ring
      _ ≤ _ := hcommon C _ hC (by rw [mul_comm]; exact hCC) (by
          nlinarith only [hM, hcr, hgt0, hvt, hgKL, hvKL, ht, hKL])
  · have hsplit : exp (-(c * r ^ α)) = exp (-(c / 2 * r ^ α)) * exp (-(c / 2 * r ^ α)) := by
      rw [← exp_add]; ring_nf
    have hCtS : 0 ≤ C * t * S := by have := mul_nonneg hC ht; positivity
    calc C * t * S * (1 + r) ^ 2 * exp ((I + 3 * w) / 2) * exp (-(c * r ^ α))
        = C * t * S * ((1 + r) ^ 2 * exp (-(c / 2 * r ^ α))) *
            exp ((I + 3 * w) / 2 + -(c / 2 * r ^ α)) := by
          rw [hsplit, exp_add]; ring
      _ ≤ C * t * S * B * exp ((I + 3 * w) / 2 + -(c / 2 * r ^ α)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB r hr0) hCtS)
            (exp_pos _).le
      _ = (C * B) * t * S * exp ((I + 3 * w) / 2 + -(c / 2 * r ^ α)) := by ring
      _ ≤ _ := hcommon (C * B) _ (mul_nonneg hC (by linarith only [hB1]))
          (by rw [← mul_assoc, mul_comm C₀ C]; exact hCB) (by
          nlinarith only [hM, hcr, hgt0, hvt, hgKL, hvKL, ht, hKL])

/-- **`eq:amplification-good-trajectory`: a good clock realization.** Let `g, c > 0`,
`v, C, C₀ ≥ 0`, `α > 0` and `K ≥ 1`. There are `C' > 0` and a threshold `N ≥ 2`
such that the following holds for every `n ≥ N`, every `𝓘, w ≥ 0` and every
`|S₀| ≤ C₀ n²`. Run the clocks for the time `t_* = (6 / g)(𝓘 + w + K log n)` and
truncate at the radius `r = ⌈(C' (t_* + K log n))^(1/α)⌉`, and put
`M₀ = exp ((𝓘 + 3w)/2)`. Let `X`, `Y` and `Z` be real random variables on one
probability space, with `Y, Z ≥ 0`, satisfying the averaged estimates
`𝔼 X² ≤ M₀² e^{-g t_*}`, `𝔼 Y ≤ C t_* |S₀| M₀ e^{v t_* - c r^α}` and
`𝔼 Z ≤ C t_* |S₀| (1 + r)² M₀ e^{-c r^α}`. Then one realization has
`X, Y, Z ≤ n^{-K}`.

In the application `X = ‖D (I - P_Ω) ζ‖`, `Y = ‖(D - D_ret) ζ‖` and
`Z = M₀ ‖D_ret - L'‖`. Source: `09-amplification.tex`, lines 453–499. -/
theorem exists_good_realization {g v c C C₀ α : ℝ} (hg : 0 < g) (hv : 0 ≤ v)
    (hc : 0 < c) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hα : 0 < α) {K : ℕ} (hK : 1 ≤ K) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ I w : ℝ, 0 ≤ I → 0 ≤ w →
      ∀ S : ℕ, (S : ℝ) ≤ C₀ * (n : ℝ) ^ 2 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X Y Z : Ω → ℝ), Integrable (fun ω ↦ X ω ^ 2) μ →
        0 ≤ᵐ[μ] Y → Integrable Y μ → 0 ≤ᵐ[μ] Z → Integrable Z μ →
        ∫ ω, X ω ^ 2 ∂μ ≤
          exp ((I + 3 * w) / 2) ^ 2 * exp (-(g * amplificationTime g I w K n)) →
        ∫ ω, Y ω ∂μ ≤
          C * amplificationTime g I w K n * S * exp ((I + 3 * w) / 2) *
            exp (v * amplificationTime g I w K n - c *
              (amplificationRadius C' α (amplificationTime g I w K n) K n : ℝ) ^ α) →
        ∫ ω, Z ω ∂μ ≤
          C * amplificationTime g I w K n * S *
            (1 + (amplificationRadius C' α (amplificationTime g I w K n) K n : ℝ)) ^ 2 *
            exp ((I + 3 * w) / 2) *
            exp (-(c * (amplificationRadius C' α (amplificationTime g I w K n) K n : ℝ) ^ α)) →
        ∃ ω, X ω ≤ ((n : ℝ) ^ K)⁻¹ ∧ Y ω ≤ ((n : ℝ) ^ K)⁻¹ ∧ Z ω ≤ ((n : ℝ) ^ K)⁻¹ := by
  obtain ⟨C', hC', N, hN2, hN⟩ := amplification_scale_bounds hg hv hc hC hC₀ hα hK
  refine ⟨C', hC', N, hN2, fun n hn I w hI hw S hS Ω _ μ _ X Y Z hXi hY0 hYi hZ0 hZi ha hb hc' ↦ ?_⟩
  obtain ⟨h1, h2, h3⟩ := hN n hn I w hI hw S hS
  set ε : ℝ := ((n : ℝ) ^ K)⁻¹ with hεdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnK : (2 : ℝ) ≤ (n : ℝ) ^ K := by
    have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hN2.trans hn
    calc (2 : ℝ) ≤ n := h2n
      _ = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ K := pow_le_pow_right₀ hn1 hK
  have hε : 0 < ε := inv_pos.mpr (by linarith only [hnK])
  have hεh : ε ≤ 1 / 2 := by
    rw [hεdef, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hnK
  refine exists_le_of_integral_sq_le_of_integral_le hε hXi hY0 hYi hZ0 hZi
    (ha.trans h1) (hb.trans h2) (hc'.trans h3) ?_
  have hε0 : ε ≠ 0 := hε.ne'
  have e1 : ε ^ 6 / ε ^ 2 = ε ^ 4 := by field_simp
  have e2 : ε ^ 3 / ε = ε ^ 2 := by field_simp
  have hsq : ε ^ 2 ≤ 1 / 4 := by nlinarith only [hε, hεh]
  have hfour : ε ^ 4 ≤ 1 / 16 := by nlinarith only [hsq, sq_nonneg ε]
  rw [e1, e2]
  linarith only [hsq, hfour]

end TNLean.PEPS.AreaLaw
