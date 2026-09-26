/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic

/-!
# The prescribed coefficient at overlap two

For auxiliary dimension four and rate \(1/1000\), the coefficient printed
in Nachtergaele, arXiv:cond-mat/9410110, Section 6, equation `boundAm`,
is strictly smaller than \(1/16\) at overlap two. The physical projection
lower bound needed to contradict that estimate is proved separately.
-/

namespace MPSTensor.FNWDimensionConstant

/-- The proposed coefficient satisfies its denominator condition but is less
than the physical lower bound of the four-dimensional example. -/
theorem dimensionFour_coefficient_lt :
    16 * (1 / 1000 : ℝ) ^ 2 < 1 ∧
      16 * (1 / 1000 : ℝ) ^ 2 * (1 + 16 * (1 / 1000 : ℝ) ^ 2) /
        (1 - 16 * (1 / 1000 : ℝ) ^ 2) < 1 / 16 := by
  norm_num

end MPSTensor.FNWDimensionConstant
