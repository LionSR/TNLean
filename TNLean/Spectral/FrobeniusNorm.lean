/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FrobeniusHilbert

/-!
# Compatibility names for Frobenius matrix geometry

The generic Frobenius squared-norm and Euclidean-space API is defined in
`TNLean.Algebra.FrobeniusHilbert`. This file retains the original
`MPSTensor` names used by the transfer-operator gap argument.
-/

open scoped Matrix BigOperators Matrix.Norms.Frobenius

namespace MPSTensor

variable {m n : ℕ}

/-- Compatibility name for the squared Frobenius norm. -/
noncomputable abbrev frobSq (X : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  Matrix.frobeniusNormSq X

/-- Compatibility form of `Matrix.frobeniusNormSq_eq_sum`. -/
lemma frobSq_eq_sum (X : Matrix (Fin m) (Fin n) ℂ) :
    frobSq X = ∑ i : Fin m, ∑ j : Fin n, ‖X i j‖ ^ 2 :=
  Matrix.frobeniusNormSq_eq_sum X

/-- Compatibility form of `Matrix.frobeniusNormSq_eq_trace`. -/
lemma frobSq_trace (X : Matrix (Fin m) (Fin n) ℂ) :
    frobSq X = (Matrix.trace (Xᴴ * X)).re :=
  Matrix.frobeniusNormSq_eq_trace X

/-- Compatibility form of `Matrix.frobeniusNormSq_smul`. -/
lemma frobSq_smul (c : ℂ) (X : Matrix (Fin m) (Fin n) ℂ) :
    frobSq (c • X) = ‖c‖ ^ 2 * frobSq X :=
  Matrix.frobeniusNormSq_smul c X

/-- Compatibility embedding with the original row-column coordinate order. -/
noncomputable abbrev matToES (M : Matrix (Fin m) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin m × Fin n) :=
  Matrix.frobeniusEquivEuclidean (Fin n) (Fin m) M.transpose

@[simp]
lemma matToES_apply (M : Matrix (Fin m) (Fin n) ℂ) (p : Fin m × Fin n) :
    matToES M p = M p.1 p.2 :=
  rfl

lemma matToES_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin m) (Fin n) ℂ) :
    matToES (∑ i ∈ s, f i) = ∑ i ∈ s, matToES (f i) := by
  simp only [matToES, Matrix.transpose_sum, map_sum]

lemma norm_matToES_sq (M : Matrix (Fin m) (Fin n) ℂ) :
    ‖matToES M‖ ^ 2 = frobSq M := by
  simp only [matToES, LinearIsometryEquiv.norm_map, Matrix.frobenius_norm_transpose, frobSq,
    Matrix.frobeniusNormSq]

/-- The Euclidean-space norm of a flattened matrix is the Frobenius norm. -/
lemma norm_matToES_eq_frobenius_norm (M : Matrix (Fin m) (Fin n) ℂ) :
    ‖matToES M‖ = ‖M‖ := by
  simp only [matToES, LinearIsometryEquiv.norm_map, Matrix.frobenius_norm_transpose]

end MPSTensor
