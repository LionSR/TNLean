/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Tactic.Linarith

/-!
# No natural number squares to one more than itself

A single generic arithmetic fact used to rule out rank-one representations of fusion rings whose
structure constant equation reads `n² = n + 1` (e.g. the Fibonacci fusion ring
`ℤ[τ]/(τ² - τ - 1)`, whose only rational solutions are the irrational golden ratio and its
conjugate).
-/

/-- **No natural number satisfies `n² = n + 1`.** -/
theorem Nat.mul_self_ne_add_one (n : ℕ) : n * n ≠ n + 1 := by
  rcases n with _ | _ | n
  · decide
  · decide
  · intro h
    nlinarith
