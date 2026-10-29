/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixUnitaryBetween
import Mathlib.Algebra.Star.StarAlgHom

/-!
# Matrix-algebra transport by a rectangular unitary

A matrix unitary between two finite coordinate spaces induces a
star-algebra equivalence of their full matrix algebras by conjugation.
The index types need not be equal. This is the matrix-coordinate adapter
used to present the actual MPU output support factors.
-/

open scoped Matrix

namespace Matrix.IsUnitaryBetween

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Conjugation by a unitary between finite coordinate spaces, as an
actual star-algebra equivalence of their full matrix algebras. -/
noncomputable def conjStarAlgEquiv (U : Matrix m n ℂ) (hU : U.IsUnitaryBetween) :
    Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix m m ℂ where
  toFun A := U * A * Uᴴ
  invFun B := Uᴴ * B * U
  left_inv A := by simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU.1,
    Matrix.one_mul, Matrix.mul_one]
  right_inv B := by simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ, hU.2,
    Matrix.one_mul, Matrix.mul_one]
  map_mul' A B := by simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU.1,
    Matrix.one_mul, Matrix.mul_one]
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_star' A := by simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  map_smul' c A := by simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- The coordinate formula for this star-algebra equivalence. -/
@[simp] theorem conjStarAlgEquiv_apply (U : Matrix m n ℂ) (hU : U.IsUnitaryBetween)
    (A : Matrix n n ℂ) : conjStarAlgEquiv U hU A = U * A * Uᴴ := rfl

end Matrix.IsUnitaryBetween
