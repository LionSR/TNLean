/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Moment radii from sharp-comparison smallness

The lower bound on the marginal parameter converts the source smallness
condition into the two moment-radius inequalities used by the sharp comparison.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Proposition 9.2, `08-scanner.tex`, lines 386–390, and Proposition 8.1,
`07-comparators.tex`, sharp-comparison clause, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The sharp-comparison smallness assumption gives both required moment
radius bounds. Source: OpenAI, *A two-dimensional area law from a global
spectral gap*, Proposition 9.2, `08-scanner.tex`, lines 386–390, and
Proposition 8.1, `07-comparators.tex`, sharp-comparison clause, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem sharpSmallness_le_moment_radius {B a c₀ : ℝ}
    (hB : 1 ≤ B) (hsmall : a * Real.sqrt B ≤ min c₀ 1 / 10) :
    10 * a ≤ c₀ / Real.sqrt B ∧ 10 * a ≤ 1 := by
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr (zero_lt_one.trans_le hB)
  have hprod : 10 * a * Real.sqrt B ≤ min c₀ 1 := by linarith only [hsmall]
  exact ⟨(le_div_iff₀ hsqrt).mpr (hprod.trans (min_le_left _ _)),
    ((le_div_iff₀ hsqrt).mpr (hprod.trans (min_le_right _ _))).trans
      ((div_le_one hsqrt).mpr (Real.one_le_sqrt.mpr hB))⟩

end TNLean.PEPS.AreaLaw.Scan
