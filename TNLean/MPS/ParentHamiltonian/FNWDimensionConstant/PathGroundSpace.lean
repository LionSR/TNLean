/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWDimensionConstant.MatrixUnitPaths

/-!
# Unmarked path vectors as open-boundary matrix-product vectors

For weighted matrix-unit tensors, fixing the external vertices of a path
is equivalent to inserting the corresponding matrix-unit boundary.
-/

open scoped BigOperators Matrix InnerProductSpace

namespace MPSTensor.FNWDimensionConstant

variable {k : ℕ}

/-- The unmarked four-edge path vector is the open-boundary vector of the
matrix unit joining its terminal vertex to its initial vertex. -/
theorem pathVector_one_eq_groundSpaceMap (t : Matrix (Fin k) (Fin k) ℝ)
    (a f : Fin k) :
    pathVector t (fun _ _ ↦ 1) a f =
      WithLp.toLp 2 (groundSpaceMap (matrixUnitTensor t) 4 (Matrix.single f a 1)) := by
  ext σ
  simp only [pathVector, WithLp.ofLp_sum, Finset.sum_apply, one_mul,
    groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord]
  simp [pathConfig, funext_iff, Fin.forall_fin_succ,
    matrixUnitTensor, Matrix.mul_apply, Matrix.single_apply]
  simp only [← finProdFinEquiv.symm_apply_eq, Prod.ext_iff]
  simp [Matrix.trace, Matrix.single_apply, ite_and]
  split_ifs <;> simp_all [mul_assoc]

end MPSTensor.FNWDimensionConstant
