/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GoodRealization

/-!
# The amplification radius is a power of the scale

With the time `t_* = C (𝓘 + w + K log n)` and the radius `r = ⌈(C' (t_* + K log n))^{1/α}⌉`
of `eq:amplification-time-choice`, the input bound `𝓘 ≤ C₀ n^{1-ε}` of
`eq:amplification-input-information` and `w = n^{3/5}` give `r ≤ C_M n^{(1-ε)/α}`, the first
half of `eq:amplification-radius`. The constant depends only on `g, C', C₀, K, α`, and is
given explicitly by `amplificationRadiusCoefficient`.

## Main statements

* `TNLean.PEPS.AreaLaw.amplificationRadius_le_coefficient_mul_rpow`.
* `TNLean.PEPS.AreaLaw.exists_amplificationRadius_le`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 455–461,
  485–486 and 563–565.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Real

namespace TNLean.PEPS.AreaLaw

/-- The coefficient `C_rad = (C' B_r)^{1/α} + 1` of the radius bound, with
`B_r = (6 / g)(C₀ + 1 + 2K / (1 - ε)) + K / (1 - ε)`. Source: `09-amplification.tex`,
lines 455–461 and 563–565. -/
noncomputable def amplificationRadiusCoefficient (g C' C₀ α ε : ℝ) (K : ℕ) : ℝ :=
  (C' * (6 / g * (C₀ + 1 + 2 * K / (1 - ε)) + K / (1 - ε))) ^ α⁻¹ + 1

/-- The radius coefficient is nonnegative. -/
theorem amplificationRadiusCoefficient_nonneg {g C' C₀ ε : ℝ} (hg : 0 < g) (hC' : 0 ≤ C')
    (hC₀ : 0 ≤ C₀) (α : ℝ) (hε : ε < 1) (K : ℕ) :
    0 ≤ amplificationRadiusCoefficient g C' C₀ α ε K := by
  have : 0 < 1 - ε := by linarith
  unfold amplificationRadiusCoefficient
  have : 0 ≤ C' * (6 / g * (C₀ + 1 + 2 * K / (1 - ε)) + K / (1 - ε)) := by positivity
  positivity

/-- **The radius bound of `eq:amplification-radius`, with an explicit constant.** For `g > 0`,
`C' ≥ 0`, `C₀ ≥ 0`, an integer `K`, `0 < α` and `0 < ε ≤ 2/5`, at every scale `n ≥ 1` and for
every input information `0 ≤ 𝓘 ≤ C₀ n^{1-ε}`, the radius chosen with `w = n^{3/5}` is at most
`amplificationRadiusCoefficient g C' C₀ α ε K · n^{(1-ε)/α}`. Source: `09-amplification.tex`,
lines 455–461 and 563–565. -/
theorem amplificationRadius_le_coefficient_mul_rpow {g C' C₀ α ε : ℝ} (hg : 0 < g)
    (hC' : 0 ≤ C') (hC₀ : 0 ≤ C₀) (hα : 0 < α) (hε : 0 < ε) (hε' : ε ≤ 2 / 5) (K : ℕ)
    (n : ℕ) (hn : 1 ≤ n) (I : ℝ) (hI0 : 0 ≤ I) (hI : I ≤ C₀ * (n : ℝ) ^ (1 - ε)) :
    (amplificationRadius C' α (amplificationTime g I ((n : ℝ) ^ ((3 : ℝ) / 5)) K n) K n : ℝ) ≤
      amplificationRadiusCoefficient g C' C₀ α ε K * (n : ℝ) ^ ((1 - ε) / α) := by
  unfold amplificationRadiusCoefficient
  set B : ℝ := 6 / g * (C₀ + 1 + 2 * K / (1 - ε)) + K / (1 - ε)
  have hε1 : 0 < 1 - ε := by linarith
  have hB : 0 ≤ B := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set m := (n : ℝ) ^ (1 - ε) with hm
  have hm1 : 1 ≤ m := one_le_rpow hn1 hε1.le
  have hw : (n : ℝ) ^ ((3 : ℝ) / 5) ≤ m := rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hlog : log n ≤ m / (1 - ε) := log_le_rpow_div hn0.le hε1
  have hlog0 : 0 ≤ log n := log_nonneg hn1
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  set t := amplificationTime g I ((n : ℝ) ^ ((3 : ℝ) / 5)) K n
  have ht : t ≤ 6 / g * (C₀ + 1 + 2 * K / (1 - ε)) * m := by
    simp only [t, amplificationTime]
    have hKlog : (K : ℝ) * log n ≤ K * (m / (1 - ε)) := mul_le_mul_of_nonneg_left hlog hK0
    have h6 : 0 ≤ 6 / g := by positivity
    calc 6 / g * (I + (n : ℝ) ^ ((3 : ℝ) / 5) + K * log n)
        ≤ 6 / g * (C₀ * m + m + K * (m / (1 - ε))) := by gcongr
      _ ≤ 6 / g * (C₀ + 1 + 2 * K / (1 - ε)) * m := by
        rw [mul_assoc]
        gcongr
        have : (K : ℝ) * (m / (1 - ε)) ≤ 2 * K / (1 - ε) * m := by
          rw [mul_div_assoc', div_mul_eq_mul_div]
          gcongr
          nlinarith
        nlinarith
  have hsum : t + K * log n ≤ B * m := by
    have hKlog : (K : ℝ) * log n ≤ K / (1 - ε) * m := by
      calc (K : ℝ) * log n ≤ K * (m / (1 - ε)) := mul_le_mul_of_nonneg_left hlog hK0
        _ = K / (1 - ε) * m := by ring
    simp only [B]
    linarith
  have ht0 : 0 ≤ t + K * log n := by
    have : 0 ≤ t := by
      simp only [t, amplificationTime]
      have := rpow_nonneg hn0.le ((3 : ℝ) / 5)
      positivity
    positivity
  have hpow : (C' * (t + K * log n)) ^ α⁻¹ ≤ (C' * B) ^ α⁻¹ * (n : ℝ) ^ ((1 - ε) / α) := by
    calc (C' * (t + K * log n)) ^ α⁻¹ ≤ (C' * (B * m)) ^ α⁻¹ := by
          gcongr
      _ = (C' * B) ^ α⁻¹ * (n : ℝ) ^ ((1 - ε) / α) := by
          rw [← mul_assoc, mul_rpow (by positivity) (by positivity), hm, ← rpow_mul hn0.le,
            div_eq_mul_inv]
  have hnpow : 1 ≤ (n : ℝ) ^ ((1 - ε) / α) := one_le_rpow hn1 (by positivity)
  have hceil := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (C' * (t + K * log n)) ^ α⁻¹)
  simp only [amplificationRadius]
  nlinarith

/-- **The radius bound of `eq:amplification-radius`.** For `g > 0`, `C' ≥ 0`, `C₀ ≥ 0`,
an integer `K`, `0 < α` and `0 < ε ≤ 2/5`, there is a constant `C` such that at every
scale `n ≥ 1` and for every input information `0 ≤ 𝓘 ≤ C₀ n^{1-ε}`, the radius chosen with
`w = n^{3/5}` is at most `C n^{(1-ε)/α}`. Source: `09-amplification.tex`, lines 455–461 and
563–565. -/
theorem exists_amplificationRadius_le {g C' C₀ α ε : ℝ} (hg : 0 < g) (hC' : 0 ≤ C')
    (hC₀ : 0 ≤ C₀) (hα : 0 < α) (hε : 0 < ε) (hε' : ε ≤ 2 / 5) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ I : ℝ, 0 ≤ I → I ≤ C₀ * (n : ℝ) ^ (1 - ε) →
      (amplificationRadius C' α (amplificationTime g I ((n : ℝ) ^ ((3 : ℝ) / 5)) K n) K n : ℝ) ≤
        C * (n : ℝ) ^ ((1 - ε) / α) :=
  ⟨_, amplificationRadiusCoefficient_nonneg hg hC' hC₀ α (by linarith) K,
    amplificationRadius_le_coefficient_mul_rpow hg hC' hC₀ hα hε hε' K⟩

end TNLean.PEPS.AreaLaw
