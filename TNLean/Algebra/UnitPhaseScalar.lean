/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Unit-modulus complex scalars

A complex number of modulus one is inverted by its conjugate, so multiplying a
matrix that is unitary between two coordinate spaces by such a scalar keeps it
unitary.

## Main results

* `Complex.mul_star_self_of_norm_eq_one`: `c * star c = 1` when `‖c‖ = 1`.
* `Matrix.IsUnitaryBetween.smul_of_norm_eq_one`: a unit-modulus multiple of a
  rectangular unitary is a rectangular unitary.
-/

namespace Complex

/-- A complex number of modulus one times its conjugate is one. -/
theorem mul_star_self_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) : c * star c = 1 := by
  rw [Complex.star_def, Complex.mul_conj', hc]
  simp

/-- The conjugate of a complex number of modulus one times the number is one. -/
theorem star_mul_self_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) : star c * c = 1 := by
  rw [mul_comm, mul_star_self_of_norm_eq_one hc]

end Complex

namespace Matrix.IsUnitaryBetween

/-- A unit-modulus multiple of a matrix that is unitary between two coordinate
spaces is again unitary between them. -/
theorem smul_of_norm_eq_one {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] {A : Matrix a b ℂ} (hA : A.IsUnitaryBetween) (c : ℂ) (hc : ‖c‖ = 1) :
    (c • A).IsUnitaryBetween := by
  constructor
  · change (c • A)ᴴ * (c • A) = 1
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.star_mul_self_of_norm_eq_one hc, one_smul]
    exact hA.1
  · change (c • A) * (c • A)ᴴ = 1
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.mul_star_self_of_norm_eq_one hc, one_smul]
    exact hA.2

end Matrix.IsUnitaryBetween
