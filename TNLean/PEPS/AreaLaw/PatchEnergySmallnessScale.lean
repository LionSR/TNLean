/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Real.Sqrt

/-!
# The filter exponent of the patch energy estimate

The total filter weight of the patch construction is
`κ = min (1 / 2) (√(Δ / (1024 * C_E)))` with energy coefficient
`C_E = 36 q² J`. It is at most one half, its quadratic energy `C_E κ²` is at
most one 1024th of the gap, and it is positive when `C_E` and the gap are.
The value depends only on `q`, `J` and `Δ`, so it is fixed before all later
geometric and variational data.

This scalar result does not prove an energy bound for a filtered vector.
In the patch argument it is applied after that bound has been established.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 338–343,
`eq:patch-kappa-choice`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS

/-- The filter exponent `κ = min {1/2, √(Δ / (1024 C_E))}` of the patch
construction, with `C_E = 36 q² J`. It depends only on the local dimension,
the interaction bound and the gap.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 338–343,
`eq:patch-kappa-choice`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
noncomputable def patchFilterExponent (q : ℕ) (J Δ : ℝ) : ℝ :=
  min (1 / 2) (Real.sqrt (Δ / (1024 * (36 * (q : ℝ) ^ 2 * J))))

/-- The filter exponent is at most one half (`03-patches.tex`, line 342). -/
theorem patchFilterExponent_le_half (q : ℕ) (J Δ : ℝ) :
    patchFilterExponent q J Δ ≤ 1 / 2 :=
  min_le_left _ _

/-- The filter exponent is positive when the energy coefficient `36 q² J` and
the gap are positive (`03-patches.tex`, lines 340–343). -/
theorem patchFilterExponent_pos {q : ℕ} {J Δ : ℝ}
    (hC : 0 < 36 * (q : ℝ) ^ 2 * J) (hΔ : 0 < Δ) :
    0 < patchFilterExponent q J Δ :=
  lt_min (by norm_num) (Real.sqrt_pos.mpr (div_pos hΔ (by positivity)))

/-- The filter exponent is positive for a nonzero local dimension and positive
interaction bound and gap (`03-patches.tex`, lines 340–343). -/
theorem patchFilterExponent_pos_of_pos {q : ℕ} {J Δ : ℝ}
    (hq : 0 < q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    0 < patchFilterExponent q J Δ :=
  patchFilterExponent_pos (by positivity) hΔ

/-- Every parameter between zero and the filter exponent has quadratic energy
`36 q² J κ²` at most one 1024th of the gap. A zero energy coefficient is
allowed.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 338–365,
`eq:patch-kappa-choice` and `eq:patch-marginal-closeness`. -/
theorem mul_sq_le_div_1024_of_le_patchFilterExponent {q : ℕ} {J Δ κ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 ≤ Δ) (hκ : 0 ≤ κ) (hle : κ ≤ patchFilterExponent q J Δ) :
    36 * (q : ℝ) ^ 2 * J * κ ^ 2 ≤ Δ / 1024 := by
  have hC : 0 ≤ 36 * (q : ℝ) ^ 2 * J := by positivity
  rcases hC.eq_or_lt with hC | hC
  · rw [← hC, zero_mul]
    positivity
  · have hsq : κ ^ 2 ≤ Δ / (1024 * (36 * (q : ℝ) ^ 2 * J)) :=
      (pow_le_pow_left₀ hκ (hle.trans (min_le_right _ _)) 2).trans_eq
        (Real.sq_sqrt (by positivity))
    rw [div_mul_eq_div_div, le_div_iff₀' hC] at hsq
    exact hsq

/-- The filter exponent itself has quadratic energy at most one 1024th of the
gap (`03-patches.tex`, lines 338–343). -/
theorem mul_patchFilterExponent_sq_le {q : ℕ} {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 ≤ Δ) :
    36 * (q : ℝ) ^ 2 * J * patchFilterExponent q J Δ ^ 2 ≤ Δ / 1024 :=
  mul_sq_le_div_1024_of_le_patchFilterExponent hJ hΔ
    (le_min (by norm_num) (Real.sqrt_nonneg _)) le_rfl

end TNLean.PEPS
