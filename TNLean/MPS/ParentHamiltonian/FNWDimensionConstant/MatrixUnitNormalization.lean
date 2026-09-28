/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWDimensionConstant.MatrixUnitPaths
import TNLean.Algebra.MatrixSingleSpan
import QICLean.Channel.KrausMap

/-!
# Normalization and injectivity of weighted matrix-unit tensors

Nonzero weights give one-site injectivity. Unit column sums of their squares
give the trace-preserving Kraus normalization.
-/

open scoped BigOperators Matrix

namespace MPSTensor.FNWDimensionConstant

/-- Nonzero weights retain every matrix unit in the span of the letters. -/
theorem matrixUnitTensor_isInjective {k : ℕ} (t : Matrix (Fin k) (Fin k) ℝ)
    (ht : ∀ i j, t i j ≠ 0) : Kraus.IsInjective (matrixUnitTensor t) := by
  apply Submodule.eq_top_of_forall_single_mem
  intro i j
  simpa [Matrix.smul_single, ht i j] using
    (Submodule.span ℂ (Set.range (matrixUnitTensor t))).smul_mem (t i j : ℂ)⁻¹
      (Submodule.subset_span (Set.mem_range_self (finProdFinEquiv (i, j))))

/-- Unit column sums of the squared weights give trace preservation. -/
theorem matrixUnitTensor_isTP {k : ℕ} (t : Matrix (Fin k) (Fin k) ℝ)
    (hcol : ∀ j, ∑ i, t i j ^ 2 = 1) : Kraus.IsTP (matrixUnitTensor t) := by
  rw [Kraus.IsTP, ← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type, matrixUnitTensor_apply, Matrix.conjTranspose_single,
    Matrix.single_mul_single_same]
  ext i j
  simp [Matrix.single_apply, Matrix.one_apply, Matrix.sum_apply, ite_and,
    ← pow_two, ← Complex.ofReal_pow, ← Complex.ofReal_sum, hcol]

end MPSTensor.FNWDimensionConstant
