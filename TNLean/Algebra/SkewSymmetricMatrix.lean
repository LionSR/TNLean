/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Skew-symmetric matrices

This file proves the parity obstruction for nonsingular skew-symmetric matrices
over a commutative ring of characteristic zero without zero divisors. In particular,
a skew-symmetric unitary matrix over such a star ring has even dimension.

## Main results

* `Matrix.det_eq_zero_of_transpose_eq_neg_of_odd_card`: a skew-symmetric matrix
  indexed by an odd-cardinality finite type has zero determinant.
* `Matrix.even_card_of_transpose_eq_neg_of_det_ne_zero`: a nonsingular
  skew-symmetric matrix has even cardinality.
* `Matrix.UnitaryGroup.even_dimension_of_transpose_eq_neg`: a skew-symmetric
  unitary matrix on `Fin d` has even dimension.

## References

* arXiv:1703.09188, Proposition `corconj`, lines 1098--1126, especially line 1125.
-/

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n]
  [CommRing R] [NoZeroDivisors R] [CharZero R]

/-- A skew-symmetric matrix over a commutative ring of characteristic zero without
zero divisors, indexed by an odd-cardinality finite type, has zero determinant.

The identity $\det A = \det A^{\mathsf T} = \det(-A) = (-1)^{|n|}\det A$ proves
the parity assertion in arXiv:1703.09188, Proposition `corconj`, line 1125. -/
theorem det_eq_zero_of_transpose_eq_neg_of_odd_card {A : Matrix n n R}
    (hA : Aᵀ = -A) (hodd : Odd (Fintype.card n)) : A.det = 0 := by
  apply CharZero.eq_neg_self_iff.mp
  calc
    A.det = Aᵀ.det := (Matrix.det_transpose A).symm
    _ = (-A).det := congrArg Matrix.det hA
    _ = (-1 : R) ^ Fintype.card n * A.det := Matrix.det_neg A
    _ = -A.det := by rw [hodd.neg_one_pow, neg_one_mul]

/-- A skew-symmetric matrix over a commutative ring of characteristic zero without
zero divisors and with nonzero determinant is indexed by a finite type of even
cardinality.

The determinant argument proves the parity assertion in arXiv:1703.09188,
Proposition `corconj`, line 1125. -/
theorem even_card_of_transpose_eq_neg_of_det_ne_zero {A : Matrix n n R}
    (hA : Aᵀ = -A) (hdet : A.det ≠ 0) : Even (Fintype.card n) := by
  rw [← Nat.not_odd_iff_even]
  exact fun hodd ↦ hdet (det_eq_zero_of_transpose_eq_neg_of_odd_card hA hodd)

namespace UnitaryGroup

/-- A skew-symmetric unitary matrix over a commutative star ring of characteristic
zero without zero divisors has even dimension.

The determinant argument proves the parity assertion in arXiv:1703.09188,
Proposition `corconj`, line 1125: the skew-symmetric case can occur only in even
dimensions. -/
theorem even_dimension_of_transpose_eq_neg {d : ℕ} [StarRing R]
    (U : Matrix.unitaryGroup (Fin d) R)
    (hU : (U : Matrix (Fin d) (Fin d) R)ᵀ = -U) : Even d := by
  simpa using even_card_of_transpose_eq_neg_of_det_ne_zero hU
    (Matrix.UnitaryGroup.det_isUnit U).ne_zero

end UnitaryGroup

end Matrix
