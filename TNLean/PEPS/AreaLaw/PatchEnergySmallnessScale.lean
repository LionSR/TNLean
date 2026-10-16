/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Real.Sqrt

/-!
# A small parameter for the patch energy estimate

For a nonnegative energy coefficient and a positive full-system gap, one may
choose a positive parameter at most one half whose quadratic energy is at
most one 1024th of the gap. The choice is uniform in all later geometric and
variational data. The coefficient is allowed to vanish.

This scalar result does not prove an energy bound for a filtered vector.
In the patch argument it is applied after that bound has been established,
with coefficient 36 q² J.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 339–365,
`eq:patch-kappa-choice`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace Real

/-- A positive scale at most one half makes any nonnegative quadratic energy
coefficient at most one 1024th of a positive spectral gap. This is an
auxiliary choice of parameter; the coefficient may vanish.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 339–365,
`eq:patch-kappa-choice` and `eq:patch-marginal-closeness`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem exists_pos_le_half_mul_sq_le_div_1024 {C Δ : ℝ}
    (hC : 0 ≤ C) (hΔ : 0 < Δ) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 2 ∧ C * κ ^ 2 ≤ Δ / 1024 := by
  rcases hC.eq_or_lt with hC | hC
  case inr =>
    refine ⟨min (1 / 2) (sqrt (Δ / 1024 / C)),
      lt_min (by norm_num) (sqrt_pos.mpr (div_pos (div_pos hΔ (by norm_num)) hC)),
      min_le_left _ _, ?_⟩
    exact (le_div_iff₀' hC).mp
      ((pow_le_pow_left₀ (le_min (by norm_num) (sqrt_nonneg (Δ / 1024 / C)))
        (min_le_right _ _) 2).trans_eq (sq_sqrt (by positivity)))
  case inl =>
    exact ⟨1 / 2, by norm_num, le_rfl, by
      simpa only [← hC, zero_mul] using
        div_nonneg hΔ.le (show (0 : ℝ) ≤ 1024 by norm_num)⟩

end Real
