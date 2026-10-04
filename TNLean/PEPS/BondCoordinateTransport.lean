/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixIsometryKronecker

/-!
# Isometric changes of the two physical bond coordinates

A virtual isometry Q carries a bond matrix X to Q X Q†. On the vector of
matrix entries this is the physical isometry Q ⊗ conjugate(Q). This identity
allows the repeated irreducible blocks in Section 7 to be returned to the
original regular-representation coordinates.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
`Papers/1001.3807/paper_v3.tex`, lines 2938–3019.
-/

open scoped Matrix Kronecker BigOperators
namespace TNLean.PEPS

variable {Out In : Type*} [Fintype Out] [Fintype In] [DecidableEq In]

omit [Fintype In] in
private theorem entrywiseConjugate_isIsometry (Q : Matrix Out In ℂ)
    (hQ : Matrix.IsIsometry Q) : Matrix.IsIsometry (Q.map star) := by
  ext i j
  have h := congrArg star (congr_fun (congr_fun hQ i) j)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    star_star, star_sum, star_mul, Matrix.one_apply, apply_ite, star_one, star_zero,
    mul_comm] using h

/-- Change both physical endpoints by a virtual isometry and its complex conjugate.
Source: SCP10, Section 7, lines 2938–3019. -/
noncomputable def bondCoordinateMatrix (Q : Matrix Out In ℂ) :
    Matrix (Out × Out) (In × In) ℂ := Q ⊗ₖ Q.map star

omit [Fintype In] in
/-- The two-endpoint coordinate change preserves the physical bond inner product.
Source: SCP10, Section 7, lines 2938–3019. -/
theorem bondCoordinateMatrix_isIsometry (Q : Matrix Out In ℂ)
    (hQ : Matrix.IsIsometry Q) : Matrix.IsIsometry (bondCoordinateMatrix Q) :=
  hQ.kronecker Q (Q.map star) (entrywiseConjugate_isIsometry Q hQ)

omit [Fintype Out] [DecidableEq In] in
/-- The physical coordinate map acts on the actual bond matrix by Q X Q†.
Source: SCP10, Section 7, lines 2938–3019. -/
theorem bondCoordinateMatrix_mulVec (Q : Matrix Out In ℂ) (X : Matrix In In ℂ) :
    bondCoordinateMatrix Q *ᵥ (fun c => X c.1 c.2) =
      fun r => (Q * X * Q.conjTranspose) r.1 r.2 := by
  classical
  ext r
  rcases r with ⟨a, b⟩
  simp only [bondCoordinateMatrix, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end TNLean.PEPS
