/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Homogeneous bounds for a natural ceiling

If a nonnegative real quantity is at most a coefficient times a scale of at
least one, rounding it upwards enlarges the coefficient by at most one.
The quantity may vanish; no separate sign assumption on the coefficient is
needed.

Auxiliary to polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
and the area-law collar estimates, `08-scanner.tex`, lines 32–41 and 705–729.
-/

namespace Nat

/-- Rounding a nonnegative quantity bounded by `A * s` preserves the scale
with coefficient `A + 1`, provided `s ≥ 1`.
Auxiliary to polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
and the area-law collar estimates, `08-scanner.tex`, lines 32–41 and 705–729. -/
theorem ceil_le_add_one_mul_of_le_mul {x A s : ℝ}
    (hx : 0 ≤ x) (hxs : x ≤ A * s) (hs : 1 ≤ s) :
    (⌈x⌉₊ : ℝ) ≤ (A + 1) * s := by
  calc
    _ ≤ x + 1 := (ceil_lt_add_one hx).le
    _ ≤ A * s + 1 := add_le_add_right hxs _
    _ ≤ A * s + s := add_le_add_left hs _
    _ = (A + 1) * s := by rw [add_mul, one_mul]

end Nat
