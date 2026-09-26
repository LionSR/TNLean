/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The singlet matrix

The matrix $Y=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ encodes the
spin-1/2 singlet $\lvert01\rangle-\lvert10\rangle$ as a coefficient matrix. It is used by
the AKLT and RVB examples in one and two dimensions.

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Appendix A,
`eq:app:singlet-Y`, `Papers/2011.12127/TN-Review-main.tex` lines 2380–2385: the singlet
matrix `Y`.

## Main definitions

* `Matrix.singletY`: the singlet matrix `Y`.

## Main results

* `Matrix.mul_singletY`: $UY=Y(\operatorname{adj}U)^T$ for every `2 × 2` matrix `U`.
* `Matrix.singletY_mul_transpose`: $YY^T=1$.
* `Matrix.adjugate_eq_star_of_mem_specialUnitaryGroup`: the adjugate of an element of
  `SU(2)` is its conjugate transpose.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

namespace Matrix

/-- Source: arXiv:2011.12127, `eq:app:singlet-Y`, `Papers/2011.12127/TN-Review-main.tex`
lines 2380–2385. The singlet matrix `Y = [[0,-1],[1,0]]`. -/
def singletY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- The entries of the singlet matrix: `Y a b` is nonzero only for `a = 1 - b`, where it
is `(-1)^b`. -/
theorem singletY_apply (a b : Fin 2) :
    singletY a b = if a = 1 - b then (-1) ^ b.val else 0 := by
  fin_cases a <;> fin_cases b <;> simp [singletY]

/-- Moving a `2 × 2` matrix through the singlet: $UY=Y(\operatorname{adj}U)^T$. -/
theorem mul_singletY (U : Matrix (Fin 2) (Fin 2) ℂ) :
    U * singletY = singletY * (adjugate U)ᵀ := by
  rw [adjugate_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [singletY, mul_apply, Fin.sum_univ_two]

/-- The singlet matrix is orthogonal: $YY^T=1$. -/
theorem singletY_mul_transpose : singletY * singletYᵀ = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [singletY, mul_apply, Fin.sum_univ_two]

/-- The adjugate of a special unitary matrix is its conjugate transpose. -/
theorem adjugate_eq_star_of_mem_specialUnitaryGroup {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ specialUnitaryGroup n ℂ) : adjugate U = star U := by
  rw [mem_specialUnitaryGroup_iff] at hU
  have h1 : star U * U = 1 := mem_unitaryGroup_iff'.mp hU.1
  calc adjugate U = (star U * U) * adjugate U := by rw [h1, one_mul]
    _ = star U := by rw [mul_assoc, mul_adjugate, hU.2, one_smul, mul_one]

end Matrix
