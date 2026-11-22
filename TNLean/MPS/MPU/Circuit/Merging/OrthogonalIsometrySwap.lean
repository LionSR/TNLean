/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Module

/-!
# Swapping orthogonal isometric images

For orthogonal isometries `J` and `V`, the matrix
`1 - (V - J) * (V - J)ᴴ` is unitary and exchanges their images.
Its entries use the isometries and their pairwise products. This is the
completion in Section 6 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`.
-/

open scoped Matrix

namespace Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [DecidableEq n] in
/-- The difference of orthogonal isometries has input Gram matrix twice the
identity. Source: the completion proof in Section 6 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
theorem gram_sub_of_orthogonal_isometries (J V : Matrix n m ℂ)
    (hJ : Jᴴ * J = 1) (hV : Vᴴ * V = 1) (hJV : Jᴴ * V = 0) :
    (V - J)ᴴ * (V - J) = (2 : ℂ) • (1 : Matrix m m ℂ) := by
  have hVJ : Vᴴ * J = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose hJV
  simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, hJ, hV, hJV, hVJ,
    sub_zero, zero_sub]
  module

/-- The reflection exchanging two orthogonal isometric images. Source:
Section 6 of `docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
def orthogonalIsometrySwap (J V : Matrix n m ℂ) : Matrix n n ℂ :=
  1 - (V - J) * (V - J)ᴴ

/-- Orthogonal isometries admit this explicit unitary exchange. Source:
Section 6 of `docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
theorem orthogonalIsometrySwap_mem_unitaryGroup (J V : Matrix n m ℂ)
    (hJ : Jᴴ * J = 1) (hV : Vᴴ * V = 1) (hJV : Jᴴ * V = 0) :
    orthogonalIsometrySwap J V ∈ unitaryGroup n ℂ := by
  let W := V - J
  have hW : Wᴴ * W = (2 : ℂ) • (1 : Matrix m m ℂ) :=
    gram_sub_of_orthogonal_isometries J V hJ hV hJV
  have hWW : (W * Wᴴ) * (W * Wᴴ) = (2 : ℂ) • (W * Wᴴ) := by
    calc
      _ = W * (Wᴴ * W) * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hW]
        simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
  change (1 - W * Wᴴ) * (1 - W * Wᴴ)ᴴ = 1
  simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
    conjTranspose_conjTranspose]
  simp only [mul_sub, sub_mul, mul_one, one_mul, hWW]
  module

/-- The exchange sends the reference isometry to the other isometry.
Only the reference Gram identity is needed for this action.
Source: Section 6 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
theorem orthogonalIsometrySwap_mul_left (J V : Matrix n m ℂ)
    (hJ : Jᴴ * J = 1) (hJV : Jᴴ * V = 0) :
    orthogonalIsometrySwap J V * J = V := by
  have hVJ : Vᴴ * J = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose hJV
  simp only [orthogonalIsometrySwap, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    conjTranspose_sub, hVJ, hJ, Matrix.mul_sub, Matrix.mul_zero, Matrix.mul_one]
  module

/-- The exchange sends the second isometry back to the reference.
Only the second Gram identity is needed for this action.
Source: Section 6 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
theorem orthogonalIsometrySwap_mul_right (J V : Matrix n m ℂ)
    (hV : Vᴴ * V = 1) (hJV : Jᴴ * V = 0) :
    orthogonalIsometrySwap J V * V = J := by
  simp only [orthogonalIsometrySwap, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    conjTranspose_sub, hJV, hV, Matrix.mul_sub, Matrix.mul_zero, Matrix.mul_one]
  module

end Matrix
