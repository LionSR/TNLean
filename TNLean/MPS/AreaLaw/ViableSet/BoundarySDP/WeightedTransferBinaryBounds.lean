/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.NatBinaryBounds
import Mathlib.Tactic.Ring

/-!
# Binary exponents for weighted transfer prefixes

The common-denominator and norm bounds for a weighted prefix give a height
whose binary exponent is polynomial in the input exponent, parameter count,
physical dimension, paired bond dimension, and prefix length.
-/

namespace TNLean.MPS.AreaLaw

/-- A local height exponent bounds the norm growth factor of a weighted
transfer matrix by an explicit power of two. -/
theorem weightedTransfer_normFactor_le_two_pow {H h Da Db q : ℕ} (hH : H ≤ 2 ^ h) :
    Da * Db * (q ^ 2 * (2 * H) ^ 3) ≤ 2 ^ (Da * Db + 2 * q + 3 * h + 3) := by
  have hq : q ^ 2 ≤ 2 ^ (2 * q) := by
    rw [Nat.mul_comm]
    exact pow_le_two_pow_mul 2 Nat.lt_two_pow_self.le
  have hdouble := mul_le_two_pow_add (show 2 ≤ 2 ^ 1 by decide) hH
  have hcube := pow_le_two_pow_mul 3 hdouble
  exact (mul_le_two_pow_add (u := Da * Db) Nat.lt_two_pow_self.le
    (mul_le_two_pow_add hq hcube)).trans (by
      apply Nat.pow_le_pow_right (by decide)
      omega)

/-- The common-denominator prefix height has an explicit polynomial binary
exponent whenever the common local height is at most `2^h`. -/
theorem weightedTransfer_prefix_height_le_two_pow {H h P t Da Db q : ℕ}
    (hH : H ≤ 2 ^ h) :
    H ^ (6 * P * t) * max 1 ((Da * Db * (q ^ 2 * (2 * H) ^ 3)) ^ t) ≤
      2 ^ ((6 * h * P + Da * Db + 2 * q + 3 * h + 3) * t) := by
  have hden : H ^ (6 * P * t) ≤ 2 ^ (6 * h * P * t) := by
    calc
      _ ≤ ((2 : ℕ) ^ h) ^ (6 * P * t) := Nat.pow_le_pow_left hH _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hnorm : (Da * Db * (q ^ 2 * (2 * H) ^ 3)) ^ t ≤
      2 ^ ((Da * Db + 2 * q + 3 * h + 3) * t) := by
    simpa only [pow_mul] using
      Nat.pow_le_pow_left (weightedTransfer_normFactor_le_two_pow hH) t
  calc
    _ ≤ 2 ^ (6 * h * P * t) * 2 ^ ((Da * Db + 2 * q + 3 * h + 3) * t) :=
      Nat.mul_le_mul hden (max_le Nat.one_le_two_pow hnorm)
    _ = _ := by rw [← pow_add]; congr 1; ring

end TNLean.MPS.AreaLaw
