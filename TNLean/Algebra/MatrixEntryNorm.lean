/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Positivity

/-!
# Entries and the operator norm of a matrix

Two comparisons between the entries of a complex matrix and its `L²` operator norm: the norm is
at most the sum of the entries weighted by the norms of the matrix units, and each entry is at
most a fixed multiple of the norm.

## Main declarations

* `Matrix.l2_opNorm_le_sum_norm_entry`
* `Matrix.exists_norm_entry_le_mul_l2_opNorm`
-/

section MatrixEntries

open scoped Matrix.Norms.L2Operator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The operator norm of a matrix is at most the sum of its entries weighted by the norms of the
matrix units. -/
theorem Matrix.l2_opNorm_le_sum_norm_entry (M : Matrix m n ℂ) :
    ‖M‖ ≤ ∑ i, ∑ j, ‖M i j‖ * ‖(Matrix.single i j 1 : Matrix m n ℂ)‖ := by
  conv_lhs => rw [M.matrix_eq_sum_single]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], norm_smul]

omit [DecidableEq m] in
/-- The entries of a matrix are bounded by a fixed multiple of its operator norm. -/
theorem Matrix.exists_norm_entry_le_mul_l2_opNorm :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Y : Matrix m n ℂ) (i : m) (j : n), ‖Y i j‖ ≤ K * ‖Y‖ := by
  let f : m → n → (Matrix m n ℂ →L[ℂ] ℂ) := fun i j =>
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  refine ⟨∑ i, ∑ j, ‖f i j‖, by positivity, fun Y i j => ?_⟩
  calc ‖Y i j‖ = ‖f i j Y‖ := rfl
    _ ≤ ‖f i j‖ * ‖Y‖ := (f i j).le_opNorm Y
    _ ≤ (∑ i, ∑ j, ‖f i j‖) * ‖Y‖ := by
        gcongr
        exact (Finset.single_le_sum (f := fun j => ‖f i j‖) (fun _ _ => by positivity)
          (Finset.mem_univ j)).trans (Finset.single_le_sum
            (f := fun i => ∑ j, ‖f i j‖) (fun _ _ => by positivity) (Finset.mem_univ i))

end MatrixEntries
