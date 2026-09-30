/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.EqualCaseGlobal
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Unitarity of block-scalar matrices

The block-scalar matrix of a periodic block family is diagonal in the flattened
bond coordinates. Unit-modulus block scalars therefore give a unitary matrix.
Source: arXiv:1708.00029, Section 4.2, lines 834--845.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {r : ℕ} {dim : Fin r → ℕ}

/-- A block-scalar matrix is diagonal in the flattened bond coordinates.
Source: arXiv:1708.00029, Section 4.2, lines 834--845. -/
theorem blockScalarMatrix_eq_diagonal (z : Fin r → ℂ) :
    blockScalarMatrix dim z =
      Matrix.diagonal (fun x => z (finSigmaFinEquiv.symm x).1) := by
  classical
  have hblock :
      (fun k : Fin r => z k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) =
        fun k => Matrix.diagonal (fun _ : Fin (dim k) => z k) := by
    funext k
    exact Matrix.smul_one_eq_diagonal (z k)
  rw [blockScalarMatrix, hblock, Matrix.blockDiagonal'_diagonal,
    Matrix.reindex_apply]
  exact Matrix.submatrix_diagonal _ _ (Equiv.injective _)

/-- Unit-modulus block scalars define a unitary on the flattened bond space.
Source: arXiv:1708.00029, Section 4.2, lines 834--845. -/
theorem blockScalarMatrix_isUnitaryBetween (z : Fin r → ℂ)
    (hz : ∀ k, ‖z k‖ = 1) :
    Matrix.IsUnitaryBetween (blockScalarMatrix dim z) := by
  classical
  have hscalar (x : Fin (∑ k : Fin r, dim k)) :
      star (z (finSigmaFinEquiv.symm x).1) * z (finSigmaFinEquiv.symm x).1 = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hz]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsIsometry, blockScalarMatrix_eq_diagonal,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    apply Matrix.diagonal_eq_one.mpr
    funext x
    exact hscalar x
  · rw [Matrix.IsCoisometry, blockScalarMatrix_eq_diagonal,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    apply Matrix.diagonal_eq_one.mpr
    funext x
    rw [mul_comm]
    exact hscalar x

end MPSTensor
