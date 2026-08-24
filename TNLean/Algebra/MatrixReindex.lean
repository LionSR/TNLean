/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Matrix identities under coordinate reindexing

This module records direct multiplication and entrywise transport identities
for matrices whose coordinate types are related by equivalences.
-/

namespace Matrix

/-- Multiplication commutes with compatible reindexings of the three
coordinate types. -/
theorem reindex_mul_reindex {R m n o m' n' o' : Type*} [Semiring R]
    [Fintype n] [Fintype n']
    (e₁ : m ≃ m') (e₂ : n ≃ n') (e₃ : o ≃ o')
    (A : Matrix m n R) (B : Matrix n o R) :
    Matrix.reindex e₁ e₂ A * Matrix.reindex e₂ e₃ B =
      Matrix.reindex e₁ e₃ (A * B) := by
  exact Matrix.reindexLinearEquiv_mul R R e₁ e₂ e₃ A B

/-- An entrywise identity in the new coordinates packages as an equality
after reindexing. -/
theorem reindex_eq_of_apply_eq {R m n m' n' : Type*}
    {A : Matrix m n R} {B : Matrix m' n' R}
    (e₁ : m ≃ m') (e₂ : n ≃ n')
    (h : ∀ i j, A (e₁.symm i) (e₂.symm j) = B i j) :
    Matrix.reindex e₁ e₂ A = B := by
  ext i j
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply] using h i j

/-- A reindexed matrix equality recovers the corresponding equality in the
original coordinates. -/
theorem apply_eq_of_reindex_eq {R m n m' n' : Type*}
    {A : Matrix m n R} {B : Matrix m' n' R}
    (e₁ : m ≃ m') (e₂ : n ≃ n')
    (h : Matrix.reindex e₁ e₂ A = B) (i : m) (j : n) :
    A i j = B (e₁ i) (e₂ j) := by
  have h' := congrFun (congrFun h (e₁ i)) (e₂ j)
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using h'

end Matrix
