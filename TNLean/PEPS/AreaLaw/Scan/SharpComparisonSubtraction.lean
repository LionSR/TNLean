/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Subtracting the sharp rates at the quarter power

The normalized terminal averages and both replica remainders remain explicit.
The upper quadratic loss contributes `12 * Kmom * a` after division by `W / 2`;
the lower loss contributes `25 * Kmom * a`. Their total is exactly 37.
No state, label, tree, selected charge point or geometric bound is constructed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, sharp comparisons, lines 171--202; `08-scanner.tex`,
lines 881--902, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- Scalar subtraction of the two rates for the same filtered norm.
Here `W = a * K`, `Gpre` and `Gpost` are the actual terminal-tree and uniform
band averages, `D = log d`, `Z = log z`, `Sent` is the selected auxiliary
entropy, and `δ` is the actual normalized excess mean energy. The physical
lower application uses `M = max 0 (2 * Sent + gmax)`.
The lower remainder is already divided by the replica count.
Source: `08-scanner.tex`, lines 881--902. -/
theorem sharp_comparison_subtraction
    {a W τ : ℝ} (ha : 0 < a) (hW : 0 < W) (hτ : 0 < τ)
    (Sent Gpre Gpost D Z Kmom δ M rate remUpper remLower : ℝ)
    (hlower : W / 2 *
        (2 * Sent + (1 - τ) * Gpre - 2 * τ * D -
          (3 + 1 / a) * Real.binEntropy τ - 25 * Kmom * a - δ / τ * M) -
        remLower ≤ rate)
    (hupper : rate ≤ 2 * D - Z + W / 2 * Gpost +
        6 * W * Kmom * a - W / (2 * a) * Z + remUpper) :
    2 * Sent + Gpre - Gpost ≤
      2 * (2 * D - Z) / W + τ * Gpre + 2 * τ * D +
        (3 + 1 / a) * Real.binEntropy τ + 37 * Kmom * a - Z / a +
          δ / τ * M + 2 * (remUpper + remLower) / W := by
  let loss := 2 * (2 * D - Z) / W + τ * Gpre + 2 * τ * D +
    (3 + 1 / a) * Real.binEntropy τ + 37 * Kmom * a - Z / a +
      δ / τ * M + 2 * (remUpper + remLower) / W
  change 2 * Sent + Gpre - Gpost ≤ loss
  apply (mul_le_mul_iff_left₀ (div_pos hW zero_lt_two)).mp
  apply sub_nonpos.mp
  calc
    (2 * Sent + Gpre - Gpost) * (W / 2) - loss * (W / 2) =
        (W / 2 *
          (2 * Sent + (1 - τ) * Gpre - 2 * τ * D -
            (3 + 1 / a) * Real.binEntropy τ - 25 * Kmom * a - δ / τ * M) -
          remLower) -
        (2 * D - Z + W / 2 * Gpost + 6 * W * Kmom * a -
          W / (2 * a) * Z + remUpper) := by
      dsimp only [loss]
      field_simp [ha.ne', hW.ne', hτ.ne']
      <;> ring
    _ ≤ 0 := sub_nonpos.mpr (hlower.trans hupper)

end TNLean.PEPS.AreaLaw.Scan
