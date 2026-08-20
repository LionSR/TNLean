/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixMulRange

/-!
# Rank-one matrices in ranges of two-sided multiplication

The theorem below is used in the rank-one step of the Wielandt proof.
-/

open scoped Matrix

namespace MPSTensor

variable {D : ℕ}

/-- A rank-one matrix belongs to the range of two-sided multiplication when its defining
vectors belong to the corresponding one-sided ranges. -/
theorem vecMulVec_mem_range_mulLeft_mulRight
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (φ ψ : Fin D → ℂ)
    (hφ : φ ∈ LinearMap.range (Matrix.toLin' P))
    (hψ : ψ ∈ LinearMap.range (Q.vecMulLinear)) :
    Matrix.vecMulVec φ ψ ∈
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) :=
  Matrix.vecMulVec_mem_range_mulLeft_mulRight P Q φ ψ hφ hψ

end MPSTensor
