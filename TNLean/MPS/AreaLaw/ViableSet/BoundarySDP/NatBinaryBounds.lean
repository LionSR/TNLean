/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Basic

/-!
# Binary bounds for natural numbers

Products, maxima and powers preserve upper bounds by powers of two with
explicit exponents.
-/

namespace TNLean.MPS.AreaLaw

/-- Multiply two power-of-two bounds by adding their exponents. -/
theorem mul_le_two_pow_add {a b u v : ℕ} (ha : a ≤ 2 ^ u) (hb : b ≤ 2 ^ v) :
    a * b ≤ 2 ^ (u + v) := by rw [Nat.pow_add]; exact Nat.mul_le_mul ha hb

/-- Bound a maximum by adding the two nonnegative exponents. -/
theorem max_le_two_pow_add {a b u v : ℕ} (ha : a ≤ 2 ^ u) (hb : b ≤ 2 ^ v) :
    max a b ≤ 2 ^ (u + v) := by
  apply max_le
  · exact Nat.le_trans ha (Nat.pow_le_pow_right (by decide) (by omega))
  · exact Nat.le_trans hb (Nat.pow_le_pow_right (by decide) (by omega))

/-- Raise a power-of-two bound to a natural power. -/
theorem pow_le_two_pow_mul {a u : ℕ} (k : ℕ) (ha : a ≤ 2 ^ u) :
    a ^ k ≤ 2 ^ (u * k) := by rw [Nat.pow_mul]; exact Nat.pow_le_pow_left ha k

end TNLean.MPS.AreaLaw
