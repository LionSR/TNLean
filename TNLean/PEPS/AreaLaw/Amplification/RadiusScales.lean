/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Exponents
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The scale of the amplified collar

The fixed amplification parameters give a radius exponent strictly smaller
than the geometric separation exponent. Consequently the collar width and
twice any admissible radius are negligible compared with that separation
scale. The large-scale threshold depends only on the radius constant and the
desired fraction of the separation scale, not on the domain or cut.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Proposition 10.2, `eq:amplification-exponents` and
`eq:amplification-radius`; the final paragraph of its proof.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Filter
open scoped Topology

namespace TNLean.PEPS.AreaLaw.Exponents

/-- The exponent of the amplification radius. Source: Proposition 10.2,
`eq:amplification-radius`. -/
def radiusExponent : ℚ := (1 - amplificationEpsilon) / alpha

/-- The fixed parameters leave a strict gap between both collar exponents and
the geometric separation exponent. Source: the last paragraph of the proof
of Proposition 10.2, `eq:amplification-radius`. -/
theorem radius_exponent_gaps :
    0 < radiusExponent ∧ 1 - amplificationEpsilon < radiusExponent ∧ radiusExponent < beta := by
  norm_num [radiusExponent, amplificationEpsilon, alpha, amplificationPower, beta, boxError]

private theorem tendsto_powerRatio_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a / (n : ℝ) ^ b) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  simpa only [Function.comp_apply, neg_sub] using Real.rpow_sub hn' a b

/-- The sum of the collar scale and twice the radius scale is negligible
relative to the geometric separation scale. Source: Proposition 10.2,
`eq:amplification-radius`, and the last paragraph of its proof. -/
theorem collar_radius_scale_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ ↦
      ((n : ℝ) ^ (1 - (amplificationEpsilon : ℝ)) +
        2 * C * (n : ℝ) ^ (radiusExponent : ℝ)) / (n : ℝ) ^ (beta : ℝ))
      atTop (𝓝 0) := by
  have ha : 1 - (amplificationEpsilon : ℝ) < (beta : ℝ) := by
    exact_mod_cast radius_exponent_gaps.2.1.trans radius_exponent_gaps.2.2
  have hg : (radiusExponent : ℝ) < (beta : ℝ) := by
    exact_mod_cast radius_exponent_gaps.2.2
  simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
    (tendsto_powerRatio_zero ha).add ((tendsto_powerRatio_zero hg).const_mul (2 * C))

/-- One threshold controls the rounded collar width and every radius with the
given power bound. The threshold depends only on `C` and `η`. Source:
Proposition 10.2, `eq:amplification-radius`, final paragraph of its proof. -/
theorem exists_collar_radius_threshold (C η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ r : ℕ,
      (r : ℝ) ≤ C * (n : ℝ) ^ (radiusExponent : ℝ) →
      (⌊(n : ℝ) ^ (1 - (amplificationEpsilon : ℝ))⌋₊ : ℝ) + 2 * r <
        η * (n : ℝ) ^ (beta : ℝ) := by
  have he := (collar_radius_scale_tendsto_zero C).eventually_lt_const hη
  obtain ⟨N, hN⟩ := he.exists_forall_of_atTop
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn r hr
  have hn' : 0 < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ))
      ((le_max_right N 2).trans hn)
  have hscale := (div_lt_iff₀ (Real.rpow_pos_of_pos hn' (beta : ℝ))).mp
    (hN n ((le_max_left N 2).trans hn))
  have hfloor := Nat.floor_le
    (Real.rpow_nonneg (Nat.cast_nonneg n) (1 - (amplificationEpsilon : ℝ)))
  linarith only [hscale, hfloor, hr]

/-- The rounded collar plus twice any eventually admissible radius is of smaller
order than the separation scale. Source: Proposition 10.2,
`eq:amplification-radius`, final paragraph of its proof. -/
theorem collar_add_radius_isLittleO (C : ℝ) (r : ℕ → ℕ)
    (hr : ∀ᶠ n : ℕ in atTop, (r n : ℝ) ≤ C * (n : ℝ) ^ (radiusExponent : ℝ)) :
    (fun n : ℕ ↦ (⌊(n : ℝ) ^ (1 - (amplificationEpsilon : ℝ))⌋₊ : ℝ) + 2 * r n)
      =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (beta : ℝ)) := by
  refine Asymptotics.IsLittleO.of_bound fun η hη ↦ ?_
  obtain ⟨N, _, hN⟩ := exists_collar_radius_threshold C η hη
  filter_upwards [eventually_ge_atTop N, hr] with n hn hrn
  have hnonneg : 0 ≤
      (⌊(n : ℝ) ^ (1 - (amplificationEpsilon : ℝ))⌋₊ : ℝ) + 2 * r n := by
    positivity
  simpa only [Real.norm_of_nonneg hnonneg,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (beta : ℝ))] using
    (hN n hn (r n) hrn).le

end TNLean.PEPS.AreaLaw.Exponents
