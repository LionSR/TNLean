/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Trace powers of Hermitian matrices

This file records the power-sum form of the finite-dimensional spectral theorem.
It includes empty index types: when the matrix dimension is zero, both sides are
empty sums.

## Main declaration

* `Matrix.IsHermitian.trace_pow_eq_sum_eigenvalues_pow`: the trace of every
  natural power is the corresponding sum of powers of the real eigenvalues.
-/

open scoped Matrix BigOperators

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- For a Hermitian matrix, the trace of every natural power is the power sum
of its Hermitian eigenvalues. -/
theorem IsHermitian.trace_pow_eq_sum_eigenvalues_pow
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    Matrix.trace (A ^ k) = ∑ i, (RCLike.ofReal (hA.eigenvalues i) : 𝕜) ^ k := by
  let U := hA.eigenvectorUnitary
  let D : Matrix ι ι 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hspec : A = (Unitary.conjStarAlgAut 𝕜 (Matrix ι ι 𝕜) U) D := by
    simpa [D, U] using hA.spectral_theorem
  calc
    Matrix.trace (A ^ k) =
        Matrix.trace (((Unitary.conjStarAlgAut 𝕜 (Matrix ι ι 𝕜) U) D) ^ k) := by
      rw [hspec]
    _ = Matrix.trace ((Unitary.conjStarAlgAut 𝕜 (Matrix ι ι 𝕜) U) (D ^ k)) := by
      rw [map_pow]
    _ = Matrix.trace (D ^ k) := by
      simp [Unitary.conjStarAlgAut_apply, D, Matrix.trace_mul_cycle]
    _ = ∑ i, (RCLike.ofReal (hA.eigenvalues i) : 𝕜) ^ k := by
      simp [D, diagonal_pow]

end Matrix
