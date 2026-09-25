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
real square root, together with the companion identity for the square of its
inverse, and names the complex number `1 / √2` with its basic identities.

## Main definitions

* `Complex.invSqrtTwo`: the complex number `1 / √2`.
-/

namespace Complex

/-- The complex coercion of the real square root of a nonnegative number squares
to that number. -/
theorem ofReal_sqrt_sq (x : ℝ) (hx : 0 ≤ x) :
    (↑(Real.sqrt x) : ℂ) ^ 2 = x := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt hx]

/-- The inverse of the complex coercion of the real square root of a nonnegative
number multiplied by itself is the inverse of that number. -/
theorem ofReal_sqrt_inv_mul_self (x : ℝ) (hx : 0 ≤ x) :
    (↑(Real.sqrt x) : ℂ)⁻¹ * (↑(Real.sqrt x) : ℂ)⁻¹ = (x : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hx]

/-- The complex number `1 / √2`, the normalization of a Hadamard-type factor. -/
noncomputable def invSqrtTwo : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The complex number `1 / √2` is nonzero. -/
theorem invSqrtTwo_ne_zero : invSqrtTwo ≠ 0 :=
  inv_ne_zero (ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 two_pos))

theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = (2 : ℂ)⁻¹ := by
  rw [invSqrtTwo, ofReal_sqrt_inv_mul_self 2 (by norm_num)]
  norm_num

/-- The square of `1 / √2` is `1 / 2`. -/
theorem invSqrtTwo_sq : invSqrtTwo ^ 2 = (2 : ℂ)⁻¹ := by
  rw [pow_two, invSqrtTwo_mul_self]

theorem invSqrtTwo_pow_mul_self (n : ℕ) :
    invSqrtTwo ^ n * invSqrtTwo ^ n * (2 : ℂ) ^ n = 1 := by
  rw [← mul_pow, ← mul_pow, invSqrtTwo_mul_self, inv_mul_cancel₀ two_ne_zero, one_pow]

/-- The complex number `1 / √2` is real, so complex conjugation fixes it. -/
@[simp] theorem conj_invSqrtTwo : starRingEnd ℂ invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo, Complex.conj_ofReal]

/-- The `star` spelling of `conj_invSqrtTwo`, for rewriting after
`Matrix.conjTranspose_smul`. -/
@[simp] theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo :=
  conj_invSqrtTwo

end Complex
