/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialBoxEstimate

/-!
# Bounds for the gain in the initial box exponent

The initial box recurrence has scale `M`, ratio `(1 - p / 2) * M²`,
and exponent `e₀ = log_M ((1 - p / 2) * M²) - 1`.
Its gain `1 - e₀` lies between `p / (2 * log M)` and
`p / ((2 - p) * log M)`. These bounds quantify the dependence of
the initial exponent on the buffer probability and scale, whose named
definitions retain the physical parameters `q, R, J, Δ`.

These are auxiliary quantitative consequences of the exponent formula;
they do not replace the source's initial entropy estimate.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 3.3, `02-initial.tex`, lines 651–667, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw

/-- The exact gain in the initial box exponent, obtained from the logarithm of the
recurrence ratio. Source: Proposition 3.3, `02-initial.tex`, lines 651–663. -/
theorem one_sub_initialBoxExponent_eq (q R : ℕ) (J Δ : ℝ) :
    1 - initialBoxExponent q R J Δ =
      -Real.log (1 - initialBoxProb q R J Δ / 2) /
        Real.log (initialBoxScale q R J Δ) := by
  have hp := (initialBoxProb_pos_and_le_half q R J Δ).2
  have hprob : 0 < 1 - initialBoxProb q R J Δ / 2 := by linarith
  have hM : (1 : ℝ) < initialBoxScale q R J Δ := by
    exact_mod_cast (show 1 < initialBoxScale q R J Δ from
      lt_of_lt_of_le (by norm_num) (sixteen_le_initialBoxScale q R J Δ))
  have hlog : Real.log (initialBoxScale q R J Δ) ≠ 0 := (Real.log_pos hM).ne'
  rw [initialBoxExponent, initialBoxRatio,
    Real.log_mul hprob.ne' (pow_ne_zero 2 (lt_trans zero_lt_one hM).ne'),
    Real.log_pow]
  simp only [Nat.cast_ofNat, add_div, mul_div_cancel_right₀ _ hlog]
  ring

/-- Two-sided bounds for the gain in the initial box exponent. They make precise the
order `p / (2 * log M)` suggested by Proposition 3.3's exponent formula
(`02-initial.tex`, lines 660–663), with `p = initialBoxProb q R J Δ` and
`M = initialBoxScale q R J Δ`. -/
theorem initialBoxExponent_gain_bounds (q R : ℕ) (J Δ : ℝ) :
    initialBoxProb q R J Δ / (2 * Real.log (initialBoxScale q R J Δ)) ≤
        1 - initialBoxExponent q R J Δ ∧
      1 - initialBoxExponent q R J Δ ≤
        initialBoxProb q R J Δ /
          ((2 - initialBoxProb q R J Δ) * Real.log (initialBoxScale q R J Δ)) := by
  let p := initialBoxProb q R J Δ
  have hp : p ≤ 1 / 2 := (initialBoxProb_pos_and_le_half q R J Δ).2
  have hprob : 0 < 1 - p / 2 := by linarith
  have hM : (1 : ℝ) < initialBoxScale q R J Δ := by
    exact_mod_cast (show 1 < initialBoxScale q R J Δ from
      lt_of_lt_of_le (by norm_num) (sixteen_le_initialBoxScale q R J Δ))
  have hlog := (Real.log_pos hM).le
  have hlower : p / 2 ≤ -Real.log (1 - p / 2) := by
    linarith [Real.log_le_sub_one_of_pos hprob]
  have hupper : -Real.log (1 - p / 2) ≤ p / (2 - p) := by
    apply (le_div_iff₀ (by linarith : 0 < 2 - p)).2
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hprob) hprob.le
    have hinv := mul_inv_cancel₀ hprob.ne'
    nlinarith
  rw [one_sub_initialBoxExponent_eq]
  constructor
  · simpa only [div_div] using div_le_div_of_nonneg_right hlower hlog
  · simpa only [div_div] using div_le_div_of_nonneg_right hupper hlog

end TNLean.PEPS.AreaLaw
