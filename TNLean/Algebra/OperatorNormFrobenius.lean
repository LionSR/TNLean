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
- `Matrix.sum_entry_norm_sq_le_card_mul_norm_sq`
- `Matrix.gramReshuffle_norm_sq_le_rectangularChoi_norm_sq`
- `Matrix.gramReshuffle_norm_sq_le_card_cube_mul_opNorm_sq`
-/

open scoped Matrix.Norms.L2Operator

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

/-- The squared Euclidean mass of one column is bounded by the squared L² operator norm. -/
theorem sum_column_norm_sq_le_norm_sq (A : Matrix α α ℂ) (j : α) :
    (∑ i, ‖A i j‖ ^ 2) ≤ ‖A‖ ^ 2 := by
  have h := A.l2_opNorm_mulVec (EuclideanSpace.single j (1 : ℂ))
  change ‖(EuclideanSpace.equiv α ℂ).symm (A *ᵥ Pi.single j 1)‖ ≤
    ‖A‖ * ‖EuclideanSpace.single j (1 : ℂ)‖ at h
  have h' : ‖(EuclideanSpace.equiv α ℂ).symm (A.col j)‖ ≤ ‖A‖ := by
    simpa using h
  simpa [EuclideanSpace.norm_sq_eq, col_apply] using
    pow_le_pow_left₀ (norm_nonneg _) h' 2

/-- The entrywise squared mass of a square matrix is at most its number of columns
multiplied by the squared L² operator norm. -/
theorem sum_entry_norm_sq_le_card_mul_norm_sq (A : Matrix α α ℂ) :
    (∑ p : α × α, ‖A p.1 p.2‖ ^ 2) ≤
      (Fintype.card α : ℝ) * ‖A‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ i, ∑ j, ‖A i j‖ ^ 2) = ∑ j, ∑ i, ‖A i j‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ _j : α, ‖A‖ ^ 2 :=
      Finset.sum_le_sum fun j _ ↦ sum_column_norm_sq_le_norm_sq A j
    _ = (Fintype.card α : ℝ) * ‖A‖ ^ 2 := by simp

/-- Every complex matrix unit has L² operator norm one. -/
theorem l2_opNorm_single_one (i j : α) :
    ‖(single i j 1 : Matrix α α ℂ)‖ = 1 := by
  apply le_antisymm
  · rw [l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    change ‖(EuclideanSpace.equiv α ℂ).symm (single i j 1 *ᵥ x)‖ ≤ 1 * ‖x‖
    rw [single_mulVec]
    change ‖EuclideanSpace.single i ((1 : ℂ) * x.ofLp j)‖ ≤ 1 * ‖x‖
    simpa using PiLp.norm_apply_le x j
  · have h := (single i j 1 : Matrix α α ℂ).l2_opNorm_mulVec
      (EuclideanSpace.single j (1 : ℂ))
    rw [single_mulVec_eq] at h
    simpa using h

/-- The squared Euclidean operator norm of the reshuffled Choi matrix is bounded by the
entrywise squared mass of the rectangular Choi matrix. -/
theorem gramReshuffle_norm_sq_le_rectangularChoi_norm_sq
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ) :
    ‖gramReshuffle Φ‖ ^ 2 ≤
      ∑ p : (α × α) × (α × α), ‖rectangularChoi Φ p.1 p.2‖ ^ 2 := by
  rw [gramReshuffle]
  exact (toEuclideanCLM_norm_sq_le_sum_norm_sq (gramReshuffleMatrix Φ)).trans_eq
    (gramReshuffleMatrix_norm_sq_eq_rectangularChoi_norm_sq Φ)

/-- Reshuffling the Choi matrix of a linear map on `α × α` matrices costs at most
`card α ^ 3` when its squared L² operator norm is compared with that of the map. -/
theorem gramReshuffle_norm_sq_le_card_cube_mul_opNorm_sq
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ) :
    ‖gramReshuffle Φ‖ ^ 2 ≤
      (Fintype.card α : ℝ) ^ 3 * ‖LinearMap.toContinuousLinearMap Φ‖ ^ 2 := by
  refine (gramReshuffle_norm_sq_le_rectangularChoi_norm_sq Φ).trans ?_
  simp_rw [Fintype.sum_prod_type]
  simp_rw [rectangularChoi_apply]
  calc
    (∑ c, ∑ e, ∑ a, ∑ b, ‖Φ (single c a 1) e b‖ ^ 2) =
        ∑ c, ∑ a, ∑ e, ∑ b, ‖Φ (single c a 1) e b‖ ^ 2 := by
      congr with c
      rw [Finset.sum_comm]
    _ ≤ ∑ _c : α, ∑ _a : α,
        (Fintype.card α : ℝ) * ‖LinearMap.toContinuousLinearMap Φ‖ ^ 2 := by
      gcongr with c a
      calc
        (∑ e, ∑ b, ‖Φ (single c a 1) e b‖ ^ 2) ≤
            (Fintype.card α : ℝ) * ‖Φ (single c a 1)‖ ^ 2 := by
          simpa only [Fintype.sum_prod_type] using
            sum_entry_norm_sq_le_card_mul_norm_sq (Φ (single c a 1))
        _ ≤ (Fintype.card α : ℝ) * ‖LinearMap.toContinuousLinearMap Φ‖ ^ 2 := by
          gcongr
          calc
            ‖Φ (single c a 1)‖ ≤ ‖LinearMap.toContinuousLinearMap Φ‖ *
                ‖(single c a 1 : Matrix α α ℂ)‖ :=
              (LinearMap.toContinuousLinearMap Φ).le_opNorm _
            _ = ‖LinearMap.toContinuousLinearMap Φ‖ := by
              rw [l2_opNorm_single_one, mul_one]
    _ = (Fintype.card α : ℝ) ^ 3 * ‖LinearMap.toContinuousLinearMap Φ‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Matrix
