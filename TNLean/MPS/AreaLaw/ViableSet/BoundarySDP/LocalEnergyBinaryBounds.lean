/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedTransferBinaryBounds

/-!
# Binary exponents for local-energy contractions

A common input denominator and a norm bound on each local contribution
give a coordinate-height estimate for finite sums of local-energy matrix
elements. Its binary exponent is polynomial in the input height exponent,
the number of parameters, the chain length, and the matrix dimensions.

## References

- LVV, arXiv:1307.5143, Claim 2.7: matrix elements for boundary minimization.
-/

namespace TNLean.MPS.AreaLaw

/-- The denominator and norm estimate for a sum of `m` two-site matrix
elements has an explicit polynomial binary exponent. -/
theorem localEnergy_height_le_two_pow {H h P n m Da Db q : ℕ} (hH : H ≤ 2 ^ h) :
    H ^ (2 * P * (3 * n + 3)) *
        max 1 (m * q ^ 4 * (2 * H) ^ 3 * (Da * Db * (q ^ 2 * (2 * H) ^ 3)) ^ n) ≤
      2 ^ (6 * h * P * (n + 1) + m * q ^ 2 + 2 * q + 3 * h + 3 +
        (Da * Db + 2 * q + 3 * h + 3) * n) := by
  have hden : H ^ (2 * P * (3 * n + 3)) ≤ 2 ^ (6 * h * P * (n + 1)) := by
    calc
      _ ≤ ((2 : ℕ) ^ h) ^ (2 * P * (3 * n + 3)) := Nat.pow_le_pow_left hH _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hlocal : m * q ^ 4 * (2 * H) ^ 3 ≤ 2 ^ (m * q ^ 2 + 2 * q + 3 * h + 3) := by
    calc
      _ = m * q ^ 2 * (q ^ 2 * (2 * H) ^ 3) := by ring
      _ ≤ _ := weightedTransfer_normFactor_le_two_pow hH
  have hnorm : m * q ^ 4 * (2 * H) ^ 3 * (Da * Db * (q ^ 2 * (2 * H) ^ 3)) ^ n ≤
      2 ^ ((m * q ^ 2 + 2 * q + 3 * h + 3) + (Da * Db + 2 * q + 3 * h + 3) * n) := by
    calc
      _ ≤ 2 ^ (m * q ^ 2 + 2 * q + 3 * h + 3) *
          (2 ^ (Da * Db + 2 * q + 3 * h + 3)) ^ n :=
        Nat.mul_le_mul hlocal
          (Nat.pow_le_pow_left (weightedTransfer_normFactor_le_two_pow hH) n)
      _ = _ := by rw [← pow_mul, ← pow_add]
  calc
    _ ≤ 2 ^ (6 * h * P * (n + 1)) *
        2 ^ ((m * q ^ 2 + 2 * q + 3 * h + 3) +
          (Da * Db + 2 * q + 3 * h + 3) * n) :=
      Nat.mul_le_mul hden (max_le Nat.one_le_two_pow hnorm)
    _ = _ := by rw [← pow_add]; congr 1; omega

end TNLean.MPS.AreaLaw
