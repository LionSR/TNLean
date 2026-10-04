/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Coordinate inclusions

An injection between finite basis indices defines an isometric inclusion of
the corresponding complex coordinate spaces. These inclusions place the
endpoint bond and physical spaces in the common direct sum of
arXiv:1010.3732, Section II.F.2, equation `eq:1d-sym:jointsym`.
-/

open scoped Matrix

namespace Matrix

/-- The matrix sending each basis vector to its injected coordinate.
Source context: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`, inclusions of the two summands. -/
def coordinateInclusion {n m : Type*} [DecidableEq m] (e : n ↪ m) : Matrix m n ℂ :=
  fun i j => if i = e j then 1 else 0

/-- A coordinate inclusion has orthonormal columns. Source context:
arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`. -/
theorem coordinateInclusion_isometry {n m : Type*} [Fintype m] [DecidableEq m]
    [DecidableEq n] (e : n ↪ m) :
    (coordinateInclusion e)ᴴ * coordinateInclusion e = 1 := by
  ext i j
  simp [coordinateInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, eq_comm]

/-- The adjoint of a coordinate inclusion extracts the selected rows.
Source context: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`, restriction to a summand. -/
theorem conjTranspose_coordinateInclusion_mul
    {n m p : Type*} [Fintype m] [DecidableEq m]
    (e : n ↪ m) (A : Matrix m p ℂ) :
    (coordinateInclusion e)ᴴ * A = A.submatrix e id := by
  ext i j
  simp [coordinateInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Multiplication by a coordinate inclusion extracts the selected columns.
Source context: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`, restriction to a summand. -/
theorem mul_coordinateInclusion
    {n m p : Type*} [Fintype m] [DecidableEq m]
    (e : n ↪ m) (A : Matrix p m ℂ) :
    A * coordinateInclusion e = A.submatrix id e := by
  ext i j
  simp [coordinateInclusion, Matrix.mul_apply]

/-- Compression by a coordinate inclusion selects its square submatrix.
Source context: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`, the endpoint bond matrices. -/
theorem coordinateInclusion_compression
    {n m : Type*} [Fintype m] [DecidableEq m]
    (e : n ↪ m) (A : Matrix m m ℂ) :
    (coordinateInclusion e)ᴴ * A * coordinateInclusion e = A.submatrix e e := by
  rw [conjTranspose_coordinateInclusion_mul, mul_coordinateInclusion]
  rfl

/-- Projection onto the included coordinates fixes a matrix supported on
those rows. Source context: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, endpoint support. -/
theorem coordinateInclusion_projection_mul_of_rowSupport
    {n m p : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (e : n ↪ m) (A : Matrix m p ℂ)
    (hA : ∀ i, i ∉ Set.range e → ∀ j, A i j = 0) :
    coordinateInclusion e * (coordinateInclusion e)ᴴ * A = A := by
  classical
  rw [Matrix.mul_assoc, conjTranspose_coordinateInclusion_mul]
  ext i j
  by_cases hi : i ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hi
    simp [coordinateInclusion, Matrix.mul_apply, e.injective.eq_iff]
  · simpa [coordinateInclusion, Matrix.mul_apply,
      show ∀ a, i ≠ e a from fun a h => hi ⟨a, h.symm⟩] using (hA i hi j).symm

/-- A row-supported square matrix intertwines the coordinate inclusion
with its compression. Source context: arXiv:1010.3732, Section II.F.2,
`eq:sym:omega-gamma`, restriction to the occupied endpoint summand. -/
theorem coordinateInclusion_intertwine_of_rowSupport
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (e : n ↪ m) (A : Matrix m m ℂ)
    (hA : ∀ i, i ∉ Set.range e → ∀ j, A i j = 0) :
    A * coordinateInclusion e = coordinateInclusion e * A.submatrix e e := by
  rw [← coordinateInclusion_compression e A, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    coordinateInclusion_projection_mul_of_rowSupport e A hA]

end Matrix
