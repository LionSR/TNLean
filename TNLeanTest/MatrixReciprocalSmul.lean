/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Field.Defs
import TNLean.Tactic.MatrixReciprocalSmul

/-!
# Tests for reciprocal scalar cancellation

These examples test both reciprocal orders on rectangular matrix products, including
separated factors. Arbitrary nested scalar actions remain uncombined.
-/

variable {R m n p : Type*} [Field R] [Fintype m] [Fintype n] [Fintype p]
  {β : R} (hβ : β ≠ 0) (A : Matrix m n R) (B : Matrix n p R)
  (C : Matrix p n R) (D : Matrix n p R) (E : Matrix p m R)

example : (β⁻¹ • A) * (β • B) = A * B := by
  simp (disch := exact hβ) only [matrix_reciprocal_smul]

example : (β • A) * (β⁻¹ • B) = A * B := by
  simp (disch := exact hβ) only [matrix_reciprocal_smul]

example : (β • A) * B * (β⁻¹ • C) = A * B * C := by
  simp (disch := exact hβ) only [matrix_reciprocal_smul]

example : A * (β • B) * C * (β⁻¹ • D) * E = A * B * C * D * E := by
  simp (disch := exact hβ) only [matrix_reciprocal_smul]

example (γ : R) : (β • A) * (γ • B) = γ • β • (A * B) := by
  simp only [matrix_reciprocal_smul]
