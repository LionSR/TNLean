/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RectangularChoi

import Mathlib.Analysis.Real.Sqrt

/-!
# Euclidean operator norm and entrywise Frobenius mass

This file bounds the Euclidean operator norm of a finite complex matrix by its
entrywise Frobenius mass. It also applies the bound to the reshuffled Choi matrix.

## Main results

- `Matrix.toEuclideanCLM_norm_sq_le_sum_norm_sq`
- `Matrix.gramReshuffle_norm_sq_le_rectangularChoi_norm_sq`
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Euclidean operator norm of a complex matrix is bounded by the sum of
its squared entry norms. -/
theorem toEuclideanCLM_norm_sq_le_sum_norm_sq (A : Matrix n n ℂ) :
    ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖ ^ 2 ≤
      ∑ p : n × n, ‖A p.1 p.2‖ ^ 2 := by
  let S := ∑ p : n × n, ‖A p.1 p.2‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hop : ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖ ≤ √S := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    rw [mul_pow, Real.sq_sqrt hS, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖∑ j, A i j * WithLp.ofLp x j‖ ^ 2) ≤
      S * ∑ j, ‖WithLp.ofLp x j‖ ^ 2
    calc
      (∑ i, ‖∑ j, A i j * WithLp.ofLp x j‖ ^ 2) ≤
          ∑ i, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖WithLp.ofLp x j‖ ^ 2 := by
        gcongr with i
        calc
          ‖∑ j, A i j * WithLp.ofLp x j‖ ^ 2 ≤
              (∑ j, ‖A i j‖ * ‖WithLp.ofLp x j‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _)
              ((norm_sum_le _ _).trans_eq (by simp only [norm_mul])) 2
          _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖WithLp.ofLp x j‖ ^ 2 :=
            Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ = S * ∑ j, ‖WithLp.ofLp x j‖ ^ 2 := by
        rw [← Finset.sum_mul]
        unfold S
        rw [Fintype.sum_prod_type]
  calc
    ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A‖ ^ 2 ≤ (√S) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = S := Real.sq_sqrt hS

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The squared Euclidean operator norm of the reshuffled Choi matrix is bounded by the
entrywise squared mass of the rectangular Choi matrix. -/
theorem gramReshuffle_norm_sq_le_rectangularChoi_norm_sq
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ) :
    ‖gramReshuffle Φ‖ ^ 2 ≤
      ∑ p : (α × α) × (α × α), ‖rectangularChoi Φ p.1 p.2‖ ^ 2 := by
  rw [gramReshuffle]
  exact (toEuclideanCLM_norm_sq_le_sum_norm_sq (gramReshuffleMatrix Φ)).trans_eq
    (gramReshuffleMatrix_norm_sq_eq_rectangularChoi_norm_sq Φ)

end Matrix
