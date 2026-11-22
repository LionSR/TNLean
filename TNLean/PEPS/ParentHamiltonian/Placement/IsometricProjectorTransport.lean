/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Regional range projectors under a scaled partial isometry

A rectangular map with Gram matrix c E transports a projector supported on E
by c⁻¹ A Q A†. This does not require surjectivity onto the ambient physical
space. It is the finite-dimensional algebra used for SCP10, Theorem 6.12.
-/

open scoped Matrix

namespace TNLean.PEPS

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Fixing every vector in a matrix range is equivalent to fixing that matrix on the left. -/
theorem matrix_mul_eq_right_of_fixes_range {P Q : Matrix m m ℂ}
    (h : ∀ x ∈ Q.mulVecLin.range, P *ᵥ x = x) : P * Q = Q := by
  classical
  ext i j
  exact congrFun (h (Q.col j) ⟨Pi.single j 1, Matrix.mulVec_single_one Q j⟩) i

/-- An idempotent matrix fixes a matrix whose range is contained in its own range. -/
theorem matrix_mul_eq_right_of_range_le {P Q : Matrix m m ℂ}
    (hP : P * P = P) (hr : Q.mulVecLin.range ≤ P.mulVecLin.range) : P * Q = Q := by
  classical
  ext i j
  have hcol : Q.col j ∈ Q.mulVecLin.range :=
    ⟨Pi.single j 1, Matrix.mulVec_single_one Q j⟩
  obtain ⟨x, hx⟩ := hr hcol
  have hfix : P *ᵥ Q.col j = Q.col j := by
    rw [← hx]
    change P *ᵥ (P *ᵥ x) = P *ᵥ x
    rw [Matrix.mulVec_mulVec, hP]
  exact congrFun hfix i

/-- Orthogonal projectors with the same range are equal. -/
theorem matrix_eq_of_isStarProjection_range_eq {P Q : Matrix m m ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hr : P.mulVecLin.range = Q.mulVecLin.range) : P = Q := by
  have hPQ : P * Q = Q := matrix_mul_eq_right_of_range_le hP.isIdempotentElem.eq hr.ge
  have hQP : Q * P = P := matrix_mul_eq_right_of_range_le hQ.isIdempotentElem.eq hr.le
  have hstar := congrArg star hPQ
  rw [star_mul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq, hQP] at hstar
  exact hstar

/-- A supported virtual projector transports to an orthogonal physical projector
through a scaled partial isometry. No ambient physical surjectivity is assumed. -/
theorem isStarProjection_smul_mul_mul_conjTranspose_of_gram
    (A : Matrix n m ℂ) {E Q : Matrix m m ℂ} {c : ℝ} (hc : c ≠ 0)
    (hA : Aᴴ * A = (c : ℂ) • E) (hQ : IsStarProjection Q) (hEQ : E * Q = Q) :
    IsStarProjection ((c : ℂ)⁻¹ • (A * Q * Aᴴ)) := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hQ' : Qᴴ = Q := hQ.isSelfAdjoint.star_eq
  apply (isStarProjection_iff').mpr
  constructor
  · have hmiddle : (A * Q * Aᴴ) * (A * Q * Aᴴ) = (c : ℂ) • (A * Q * Aᴴ) := by
      calc
        _ = A * Q * (Aᴴ * A) * Q * Aᴴ := by simp only [Matrix.mul_assoc]
        _ = (c : ℂ) • (A * (Q * (E * Q)) * Aᴴ) := by
          rw [hA]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = _ := by rw [hEQ, hQ.isIdempotentElem.eq]
    rw [smul_mul_smul_comm, hmiddle, smul_smul]
    congr 1
    field_simp
  · change ((c : ℂ)⁻¹ • (A * Q * Aᴴ))ᴴ = _
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hQ', Matrix.mul_assoc]
    congr 1
    simp

/-- The transported projector intertwines the original rectangular map with Q. -/
theorem smul_mul_mul_conjTranspose_mul_of_gram
    (A : Matrix n m ℂ) {E Q : Matrix m m ℂ} {c : ℝ} (hc : c ≠ 0)
    (hA : Aᴴ * A = (c : ℂ) • E) (hQE : Q * E = Q) :
    ((c : ℂ)⁻¹ • (A * Q * Aᴴ)) * A = A * Q := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hA,
    Matrix.mul_smul, Matrix.mul_smul, hQE, smul_smul,
    inv_mul_cancel₀ hc', one_smul]

/-- The rectangular sandwich has exactly the transported virtual range. -/
theorem range_smul_mul_mul_conjTranspose_of_gram
    (A : Matrix n m ℂ) {E Q : Matrix m m ℂ} {c : ℝ} (hc : c ≠ 0)
    (hA : Aᴴ * A = (c : ℂ) • E) (hQ : IsStarProjection Q)
    (hQE : Q * E = Q) :
    (Matrix.mulVecLin ((c : ℂ)⁻¹ • (A * Q * Aᴴ))).range =
      Q.mulVecLin.range.map A.mulVecLin := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨Q *ᵥ ((c : ℂ)⁻¹ • (Aᴴ *ᵥ x)), ⟨_, rfl⟩, ?_⟩
    change A *ᵥ (Q *ᵥ ((c : ℂ)⁻¹ • (Aᴴ *ᵥ x))) =
      ((c : ℂ)⁻¹ • (A * Q * Aᴴ)) *ᵥ x
    simp only [Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · rintro y ⟨z, ⟨x, rfl⟩, rfl⟩
    refine ⟨A *ᵥ (Q *ᵥ x), ?_⟩
    change ((c : ℂ)⁻¹ • (A * Q * Aᴴ)) *ᵥ (A *ᵥ (Q *ᵥ x)) = A *ᵥ (Q *ᵥ x)
    rw [Matrix.mulVec_mulVec, smul_mul_mul_conjTranspose_mul_of_gram A hc hA hQE,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ.isIdempotentElem.eq]
    exact Matrix.mulVec_mulVec _ _ _ |>.symm

end TNLean.PEPS
