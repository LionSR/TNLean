/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixIsometryKronecker
import TNLean.MPS.MPU.Examples.ShiftSourceFormulas

/-!
# Unitarity of the shift-example swap matrices

This module proves unitarity of the four-spin matrices displayed in
arXiv:1703.09188, equations `eq:uv2_U2` and `eq:uv2_U3` (lines 2018--2034).
-/

open scoped Matrix Kronecker

namespace MPOTensor

private def fourSpinAssocEquiv (d : ℕ) :
    ((Fin d × (Fin d × Fin d)) × Fin d) ≃
      ((Fin d × Fin d) × (Fin d × Fin d)) where
  toFun x := ((x.1.1, x.1.2.1), (x.1.2.2, x.2))
  invFun x := ((x.1.1, (x.1.2, x.2.1)), x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def identitySwapIdentityKronecker (d : ℕ) :
    Matrix ((Fin d × (Fin d × Fin d)) × Fin d)
      ((Fin d × (Fin d × Fin d)) × Fin d) ℂ :=
  ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Matrix.swapMatrix d) ⊗ₖ
    (1 : Matrix (Fin d) (Fin d) ℂ)

private theorem one_isUnitaryBetween (d : ℕ) :
    (1 : Matrix (Fin d) (Fin d) ℂ).IsUnitaryBetween :=
  ⟨by simp [Matrix.IsIsometry], by simp [Matrix.IsCoisometry]⟩

private theorem swapMatrix_isUnitaryBetween (d : ℕ) :
    (Matrix.swapMatrix d).IsUnitaryBetween := by
  constructor <;>
    simp [Matrix.IsIsometry, Matrix.IsCoisometry,
      Matrix.swapMatrix_conjTranspose, Matrix.swapMatrix_mul_self]

/-- The displayed matrix $\Id\otimes\mathbb S\otimes\Id$ is unitary.

Source: arXiv:1703.09188, equations `eq:uv2_U2` and `eq:uv2_U3`
(lines 2018--2034). -/
theorem identitySwapIdentityMatrix_isUnitaryBetween (d : ℕ) :
    (identitySwapIdentityMatrix d).IsUnitaryBetween := by
  have hOne := one_isUnitaryBetween d
  have hSwap := swapMatrix_isUnitaryBetween d
  have hFirst :
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Matrix.swapMatrix d).IsIsometry :=
    Matrix.IsIsometry.kronecker _ _ hOne.1 hSwap.1
  have hRawIso : (identitySwapIdentityKronecker d).IsIsometry :=
    Matrix.IsIsometry.kronecker _ _ hFirst hOne.1
  have hRaw : (identitySwapIdentityKronecker d).IsUnitaryBetween :=
    hRawIso.isUnitaryBetween_of_card_eq _ rfl
  have hReindexed := Matrix.IsUnitaryBetween.reindex _ hRaw
    (fourSpinAssocEquiv d) (fourSpinAssocEquiv d)
  convert hReindexed using 1
  ext ⟨⟨a, b⟩, ⟨c, e⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩
  by_cases ha : a = i <;> by_cases hb : b = k <;>
    by_cases hc : c = j <;> by_cases he : e = l <;>
    simp [identitySwapIdentityMatrix, identitySwapIdentityKronecker,
      fourSpinAssocEquiv, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.swapMatrix_apply, ha, hb, hc, he]

/-- The displayed matrix $\mathbb S\otimes\mathbb S$ is unitary.

Source: arXiv:1703.09188, equations `eq:uv2_U2` and `eq:uv2_U3`
(lines 2018--2034). -/
theorem swapTensorSwapMatrix_isUnitaryBetween (d : ℕ) :
    (swapTensorSwapMatrix d).IsUnitaryBetween := by
  have hSwap := swapMatrix_isUnitaryBetween d
  have hIso : (swapTensorSwapMatrix d).IsIsometry :=
    Matrix.IsIsometry.kronecker _ _ hSwap.1 hSwap.1
  exact hIso.isUnitaryBetween_of_card_eq _ rfl

/-- The displayed matrix
$(\mathbb S\otimes\mathbb S)(\Id\otimes\mathbb S\otimes\Id)$ is unitary.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2021--2026). -/
theorem swapTensorSwapMatrix_mul_identitySwapIdentityMatrix_isUnitaryBetween
    (d : ℕ) :
    (swapTensorSwapMatrix d * identitySwapIdentityMatrix d).IsUnitaryBetween :=
  Matrix.IsUnitaryBetween.mul _ _ (swapTensorSwapMatrix_isUnitaryBetween d)
    (identitySwapIdentityMatrix_isUnitaryBetween d)

/-- The displayed matrix
$(\Id\otimes\mathbb S\otimes\Id)(\mathbb S\otimes\mathbb S)$ is unitary.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2030--2034). -/
theorem identitySwapIdentityMatrix_mul_swapTensorSwapMatrix_isUnitaryBetween
    (d : ℕ) :
    (identitySwapIdentityMatrix d * swapTensorSwapMatrix d).IsUnitaryBetween :=
  Matrix.IsUnitaryBetween.mul _ _ (identitySwapIdentityMatrix_isUnitaryBetween d)
    (swapTensorSwapMatrix_isUnitaryBetween d)

end MPOTensor
