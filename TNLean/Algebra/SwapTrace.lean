/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.MaximallyEntangled
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Trace contraction with the swap matrix

This file proves the trace identity used to contract a swap operator against a
Kronecker product.

## Main results

* `Matrix.trace_swapMatrix_mul_kronecker`: the swap contraction equals the trace of the
  product of the two factors.
* `Matrix.trace_swapMatrix_mul_kronecker_conjTranspose_of_mem_unitaryGroup`: the
  contraction of a unitary with its conjugate transpose equals its dimension.

## References

* [J. I. Cirac et al., *Matrix product unitaries: structure, symmetries, and topological
  invariants*, arXiv:1703.09188, lines 1608--1610][Cirac2017MPU]
-/

open scoped Matrix Kronecker
open Matrix Finset BigOperators

namespace Matrix

variable {n : ℕ}

/-- Contracting the swap matrix with a Kronecker product gives the trace of the product,
with the factor order used in arXiv:1703.09188, lines 1608--1610. -/
theorem trace_swapMatrix_mul_kronecker
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (swapMatrix n * (A ⊗ₖ B)).trace = (A * B).trace := by
  classical
  have hinner (i j k : Fin n) :
      (∑ l : Fin n, (if i = l ∧ j = k then 1 else 0) * (A k i * B l j)) =
        if j = k then A k i * B i j else 0 := by
    by_cases hjk : j = k
    · subst k
      simp
    · simp [hjk]
  have hmiddle (i j : Fin n) :
      (∑ k : Fin n, if j = k then A k i * B i j else 0) = A j i * B i j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [Ne.symm hkj]
    · simp
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        (if i = l ∧ j = k then 1 else 0) * (A k i * B l j)) =
      ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if j = k then A k i * B i j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        exact hinner i j k
      _ = ∑ i : Fin n, ∑ j : Fin n, A j i * B i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hmiddle i j
      _ = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
        rw [Finset.sum_comm]
  simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    swapMatrix_apply, Matrix.kroneckerMap_apply] using hsum

/-- For a unitary matrix, contracting the swap matrix with the Kronecker product of the
matrix and its conjugate transpose gives the matrix dimension. -/
theorem trace_swapMatrix_mul_kronecker_conjTranspose_of_mem_unitaryGroup
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ∈ unitaryGroup (Fin n) ℂ) :
    (swapMatrix n * (A ⊗ₖ Aᴴ)).trace = (n : ℂ) := by
  rw [trace_swapMatrix_mul_kronecker]
  have hunit : A * Aᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hA
  rw [hunit, Matrix.trace_one, Fintype.card_fin]

end Matrix
