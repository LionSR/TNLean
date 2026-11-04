/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalTensorApproximation

/-!
# Bit bounds for dyadic tensor approximation

The contraction bound is exponential in the chain length, but only its binary
logarithm enters the dyadic precision. Bounding the physical dimension, bond
dimension and inverse target error by powers of two gives an explicit linear
bound for the precision exponent.
-/

namespace TNLean.MPS.AreaLaw

/-- An exponential contraction bound and a dyadic lower error target give an
additive bound for the precision exponent. -/
theorem clog_natCeil_div_le_of_dyadic_bounds
    {K ε : ℝ} {u r : ℕ} (hK : K ≤ 2 ^ u) (hε : (2 ^ r : ℝ)⁻¹ ≤ ε) :
    Nat.clog 2 ⌈K / ε⌉₊ ≤ u + r := by
  have hεpos : 0 < ε := lt_of_lt_of_le (by positivity) hε
  apply Nat.clog_le_of_le_pow
  apply Nat.ceil_le.mpr
  push_cast
  apply (div_le_iff₀ hεpos).mpr
  calc
    K ≤ (2 : ℝ) ^ u := hK
    _ = (2 : ℝ) ^ (u + r) * (2 ^ r : ℝ)⁻¹ := by
      rw [pow_add, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
    _ ≤ (2 : ℝ) ^ (u + r) * ε :=
      mul_le_mul_of_nonneg_left hε (by positivity)

/-- Power-of-two dimension bounds control the open-chain contraction constant. -/
theorem tensor_contraction_constant_le_two_pow
    {q D a c k : ℕ} (hq : q ≤ 2 ^ a) (hD : D ≤ 2 ^ c) :
    (q ^ k : ℝ) * (D : ℝ) ^ (k + 1) * (k + 1) * 2 ^ k ≤
      2 ^ (a * k + c * (k + 1) + (k + 1) + k) := by
  have hq' : (q : ℝ) ≤ 2 ^ a := by exact_mod_cast hq
  have hD' : (D : ℝ) ≤ 2 ^ c := by exact_mod_cast hD
  have hk : (k + 1 : ℝ) ≤ 2 ^ (k + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := k + 1)).le
  calc
    (q ^ k : ℝ) * (D : ℝ) ^ (k + 1) * (k + 1) * 2 ^ k ≤
        ((2 : ℝ) ^ a) ^ k * ((2 : ℝ) ^ c) ^ (k + 1) *
          2 ^ (k + 1) * 2 ^ k := by gcongr
    _ = 2 ^ (a * k + c * (k + 1) + (k + 1) + k) := by
      simp only [← pow_mul, ← pow_add]

/-- The precision exponent is bounded by the chain length times the binary
dimension bounds, plus the accuracy exponent. -/
theorem tensor_dyadic_precision_le_of_dimension_bounds
    {q D a c k r : ℕ} {ε : ℝ} (hq : q ≤ 2 ^ a) (hD : D ≤ 2 ^ c)
    (hε : (2 ^ r : ℝ)⁻¹ ≤ ε) :
    Nat.clog 2 ⌈(q ^ k : ℝ) * (D : ℝ) ^ (k + 1) * (k + 1) * 2 ^ k / ε⌉₊ ≤
      a * k + c * (k + 1) + (k + 1) + k + r :=
  clog_natCeil_div_le_of_dyadic_bounds
    (tensor_contraction_constant_le_two_pow hq hD) hε

end TNLean.MPS.AreaLaw
