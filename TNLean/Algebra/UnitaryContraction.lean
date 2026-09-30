/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Cancellation of a unitary at a contracted matrix coordinate -/

namespace Matrix

/-- A unitary and its adjoint cancel between rectangular matrix factors. -/
theorem mul_unitary_adjoint_mul_cancel {ι κ n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] [StarRing R]
    (A : Matrix ι n R) (B : Matrix n κ R) (z : unitaryGroup n R) :
    (A * (z : Matrix n n R)ᴴ) * ((z : Matrix n n R) * B) = A * B := by
  have hz : (z : Matrix n n R)ᴴ * (z : Matrix n n R) = 1 := z.2.1
  calc
    _ = A * ((z : Matrix n n R)ᴴ * (z : Matrix n n R)) * B := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hz, Matrix.mul_one]

end Matrix
