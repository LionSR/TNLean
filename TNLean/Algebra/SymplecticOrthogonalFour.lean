/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# A four-dimensional symplectic congruence

Let `Y = [[0,1],[-1,0]]`. The matrix
`R = (1-i)/2 * (I₄ + i (Y ⊗ Y))` is unitary and carries `Y ⊗ Y` to the
identity by transpose congruence. These are the explicit matrix identities in
arXiv:1703.09188, `paper_v2.tex` lines 1165--1185, used in the reduction of
the symplectic case of the conjugation classification to orthogonal unitaries.
-/

open scoped Kronecker

namespace Matrix

/-- The two-dimensional skew-symmetric matrix `Y` of arXiv:1703.09188,
`paper_v2.tex` lines 1115--1123 and 1172--1178. -/
def symplecticY : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The four-dimensional matrix `R = (1-i)/2 (I₄ + i(Y ⊗ Y))` of
arXiv:1703.09188, `paper_v2.tex` lines 1172--1181. The product coordinates
follow the tensor-factor order in that formula. -/
noncomputable def symplecticOrthogonalR : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((1 - Complex.I) / 2) • (1 + Complex.I • (symplecticY ⊗ₖ symplecticY))

/-- The explicit matrix `R` is unitary and satisfies the transpose congruence
`Rᵀ (Y ⊗ Y) R = I₄`; see arXiv:1703.09188, `paper_v2.tex` lines 1172--1185. -/
lemma symplecticOrthogonalR_identities :
    symplecticOrthogonalRᴴ * symplecticOrthogonalR = 1 ∧
      symplecticOrthogonalRᵀ * (symplecticY ⊗ₖ symplecticY) *
        symplecticOrthogonalR = 1 := by
  constructor
  · ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      norm_num [symplecticOrthogonalR, symplecticY, Matrix.mul_apply,
        Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
      ring_nf <;> norm_num [Complex.I_sq]
  · ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      norm_num [symplecticOrthogonalR, symplecticY, Matrix.mul_apply,
        Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
      ring_nf <;> norm_num [Complex.I_sq] <;> ring

end Matrix
