/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Manufacturing a rank-one matrix in the range of two-sided multiplication

This file proves a lemma used in the rank-one step of the Wielandt proof:

If a column vector `φ` lies in the range of left-multiplication by `P` (as a linear map on
vectors), and a row vector `ψ` lies in the range of right-multiplication by `Q` (again as a
linear map on vectors), then the rank-one matrix `Matrix.vecMulVec φ ψ` lies in the range of the
(two-sided) linear map `X ↦ P * X * Q`.
-/

open scoped Matrix

namespace MPSTensor

variable {D : ℕ}

theorem vecMulVec_mem_range_mulLeft_mulRight
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (φ ψ : Fin D → ℂ)
    (hφ : φ ∈ LinearMap.range (Matrix.toLin' P))
    (hψ : ψ ∈ LinearMap.range (Q.vecMulLinear)) :
    Matrix.vecMulVec φ ψ ∈
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) := by
  -- Pick `y` with `P *ᵥ y = φ` and `z` with `z ᵥ* Q = ψ`.
  rcases (LinearMap.mem_range).1 hφ with ⟨y, hy⟩
  rcases (LinearMap.mem_range).1 hψ with ⟨z, hz⟩
  have hy' : P *ᵥ y = φ := by
    simpa [Matrix.toLin'_apply] using hy
  have hz' : z ᵥ* Q = ψ := by
    simpa [Matrix.vecMulLinear_apply] using hz
  -- Witness `X := Matrix.vecMulVec y z`.
  refine (LinearMap.mem_range).2 ?_
  refine ⟨Matrix.vecMulVec y z, ?_⟩
  -- Compute `P * (X * Q)` as a rank-one matrix.
  calc
    ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) (Matrix.vecMulVec y z)
        = P * (Matrix.vecMulVec y z * Q) := by
          simp [LinearMap.comp_apply]
    _ = P * Matrix.vecMulVec y (z ᵥ* Q) := by
          simp [Matrix.vecMulVec_mul]
    _ = Matrix.vecMulVec (P *ᵥ y) (z ᵥ* Q) := by
          simp [Matrix.mul_vecMulVec]
    _ = Matrix.vecMulVec φ ψ := by
          simp [hy', hz']

end MPSTensor
