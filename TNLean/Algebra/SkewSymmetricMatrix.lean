/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Skew-symmetric matrices

This file proves the parity obstruction for nonsingular complex skew-symmetric
matrices. In particular, a complex skew-symmetric unitary matrix has even
dimension.

## Main results

* `Matrix.det_eq_zero_of_transpose_eq_neg_of_odd_card`: a complex skew-symmetric
  matrix indexed by an odd-cardinality finite type has zero determinant.
* `Matrix.even_card_of_transpose_eq_neg_of_det_ne_zero`: a nonsingular complex
  skew-symmetric matrix has even cardinality.
* `Matrix.UnitaryGroup.even_dimension_of_transpose_eq_neg`: a skew-symmetric
  unitary matrix on `Fin d` has even dimension.

## References

* arXiv:1703.09188, Proposition `corconj`, lines 1098--1126, especially line 1125.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complex skew-symmetric matrix indexed by an odd-cardinality finite type has
zero determinant.

This is the determinant argument used in arXiv:1703.09188, Proposition `corconj`,
lines 1098--1126: $\det A = \det A^{\mathsf T} = \det(-A) = (-1)^{|n|}\det A$. -/
theorem det_eq_zero_of_transpose_eq_neg_of_odd_card {A : Matrix n n ℂ}
    (hA : Aᵀ = -A) (hodd : Odd (Fintype.card n)) : A.det = 0 := by
  apply CharZero.eq_neg_self_iff.mp
  calc
    A.det = Aᵀ.det := (Matrix.det_transpose A).symm
    _ = (-A).det := congrArg Matrix.det hA
    _ = (-1 : ℂ) ^ Fintype.card n * A.det := Matrix.det_neg A
    _ = -A.det := by rw [hodd.neg_one_pow, neg_one_mul]

/-- A complex skew-symmetric matrix with nonzero determinant is indexed by a finite
type of even cardinality.

This is the nonsingular form of the parity obstruction in arXiv:1703.09188,
Proposition `corconj`, lines 1098--1126. -/
theorem even_card_of_transpose_eq_neg_of_det_ne_zero {A : Matrix n n ℂ}
    (hA : Aᵀ = -A) (hdet : A.det ≠ 0) : Even (Fintype.card n) := by
  rw [← Nat.not_odd_iff_even]
  exact fun hodd ↦ hdet (det_eq_zero_of_transpose_eq_neg_of_odd_card hA hodd)

namespace UnitaryGroup

/-- A complex skew-symmetric unitary matrix has even dimension.

This is the parity obstruction stated at arXiv:1703.09188, Proposition `corconj`,
line 1125: the skew-symmetric case can occur only in even dimensions. -/
theorem even_dimension_of_transpose_eq_neg {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (hU : (U : Matrix (Fin d) (Fin d) ℂ)ᵀ = -U) : Even d := by
  simpa using even_card_of_transpose_eq_neg_of_det_ne_zero hU
    (Matrix.UnitaryGroup.det_isUnit U).ne_zero

end UnitaryGroup

end Matrix
