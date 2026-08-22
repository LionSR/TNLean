/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic

/-!
# Real square roots in the complex numbers

This file records the square identity for the complex coercion of a nonnegative
real square root.
-/

namespace Complex

/-- The complex coercion of the real square root of a nonnegative number squares
to that number. -/
theorem ofReal_sqrt_sq (x : ℝ) (hx : 0 ≤ x) :
    (↑(Real.sqrt x) : ℂ) ^ 2 = x := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt hx]

end Complex
