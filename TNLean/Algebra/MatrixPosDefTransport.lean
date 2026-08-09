/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive-definite transport by rectangular unitary matrices

This module records the positive-definite congruence needed when an isometric
inclusion is known to fill its ambient finite-dimensional space.
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {m n : Type*} [Finite m] [Fintype n] [DecidableEq m]

/-- Conjugating a positive-definite matrix by a rectangular matrix with a
right inverse given by its conjugate transpose preserves positive definiteness. -/
theorem PosDef.mul_mul_conjTranspose_of_mul_conjTranspose_eq_one
    {A : Matrix n n ℂ} (hA : A.PosDef) (V : Matrix m n ℂ)
    (hV : V * Vᴴ = 1) : (V * A * Vᴴ).PosDef := by
  letI := Fintype.ofFinite m
  apply hA.mul_mul_conjTranspose_same
  intro x y hxy
  have := congrArg (fun z => Matrix.vecMul z Vᴴ) hxy
  simpa [Matrix.vecMul_vecMul, hV] using this

end Matrix
