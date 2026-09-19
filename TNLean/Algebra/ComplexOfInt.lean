/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Push

/-!
# Integer matrices over the complex numbers

Entrywise coercion from integer to complex matrices preserves matrix arithmetic,
finite sums, submatrices, and Kronecker products, and is injective.
-/

open scoped Matrix Kronecker

namespace MPSTensor

/-! ### Entrywise coercion of integer matrices -/

/-- The entrywise coercion of an integer matrix into the complex matrices. -/
def complexOfInt {m n : Type*} (X : Matrix m n ℤ) : Matrix m n ℂ :=
  X.map (Int.cast)

@[simp] theorem complexOfInt_apply {m n : Type*} (X : Matrix m n ℤ) (i : m) (j : n) :
    complexOfInt X i j = (X i j : ℂ) := rfl

theorem complexOfInt_mul {m n o : Type*} [Fintype n] (X : Matrix m n ℤ) (Y : Matrix n o ℤ) :
    complexOfInt (X * Y) = complexOfInt X * complexOfInt Y := by
  ext i j
  simp only [complexOfInt_apply, Matrix.mul_apply]
  push_cast
  rfl

theorem complexOfInt_one {n : Type*} [DecidableEq n] :
    complexOfInt (1 : Matrix n n ℤ) = 1 := by
  ext i j
  simp only [complexOfInt_apply, Matrix.one_apply]
  split <;> simp

theorem complexOfInt_neg {m n : Type*} (X : Matrix m n ℤ) :
    complexOfInt (-X) = -complexOfInt X := by
  ext i j
  simp only [complexOfInt_apply, Matrix.neg_apply, Int.cast_neg]

/-- The coercion of the zero matrix is the zero matrix. -/
theorem complexOfInt_zero {m n : Type*} : complexOfInt (0 : Matrix m n ℤ) = 0 := by
  ext i j
  simp [complexOfInt]

theorem complexOfInt_add {m n : Type*} (X Y : Matrix m n ℤ) :
    complexOfInt (X + Y) = complexOfInt X + complexOfInt Y := by
  ext i j
  simp [complexOfInt]

theorem complexOfInt_zsmul {m n : Type*} (c : ℤ) (X : Matrix m n ℤ) :
    complexOfInt (c • X) = (c : ℂ) • complexOfInt X := by
  ext i j
  simp [complexOfInt]

theorem complexOfInt_sum {m n κ : Type*} (t : Finset κ) (f : κ → Matrix m n ℤ) :
    complexOfInt (∑ x ∈ t, f x) = ∑ x ∈ t, complexOfInt (f x) := by
  ext i j
  simp [complexOfInt, Matrix.sum_apply]

theorem complexOfInt_submatrix {m n m' n' : Type*} (X : Matrix m n ℤ) (f : m' → m)
    (g : n' → n) : complexOfInt (X.submatrix f g) = (complexOfInt X).submatrix f g := rfl

theorem complexOfInt_kronecker {m n m' n' : Type*} (X : Matrix m n ℤ) (Y : Matrix m' n' ℤ) :
    complexOfInt (X ⊗ₖ Y) = complexOfInt X ⊗ₖ complexOfInt Y := by
  ext i j
  simp [complexOfInt]

theorem complexOfInt_injective {m n : Type*} :
    Function.Injective (complexOfInt (m := m) (n := n)) := by
  intro X Y h
  ext i j
  have hij := congrFun (congrFun h i) j
  simpa only [complexOfInt_apply, Int.cast_inj] using hij

end MPSTensor
