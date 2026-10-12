/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Matrices acting on Euclidean vectors

A complex matrix `A` with rows indexed by `m` and columns indexed by `n` acts on Euclidean
vectors as the continuous linear map `ψ ↦ A ψ` from `ℂ^n` to `ℂ^m` (`act`). This one action is
used both for vectors on the sheets of encoded frames and for the local maps of the register
calculus, where operators are composed as continuous linear maps.

## Main definitions

* `EncodedFrame.act`: a matrix as a continuous linear map of Euclidean spaces.

## Main results

* `EncodedFrame.act_apply`, `EncodedFrame.act_apply_apply`, `EncodedFrame.ofLp_act`: the action
  is matrix-vector multiplication.
* `EncodedFrame.act_single_apply`: the action on a standard basis vector is a column.
* `EncodedFrame.norm_act`: the operator norm of the action is the operator norm of the matrix.
* `EncodedFrame.act_mul`: products of matrices act by composition.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.EncodedFrame

variable {l m n : Type*} [Fintype m] [Fintype n]

/-- The action of a matrix on Euclidean vectors, as a continuous linear map `ℂ^n → ℂ^m`. -/
def act (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℂ (m → ℂ)).symm.toLinearMap ∘ₗ A.mulVecLin ∘ₗ
      (WithLp.linearEquiv 2 ℂ (n → ℂ)).toLinearMap)

/-- The action of `A` on `ψ` is the vector `A *ᵥ ψ`. -/
theorem act_apply (A : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    act A ψ = WithLp.toLp 2 (A *ᵥ ψ) :=
  rfl

/-- The coordinates of `act A ψ` are `A *ᵥ ψ`. -/
theorem ofLp_act (A : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    (act A ψ).ofLp = A *ᵥ ψ.ofLp :=
  rfl

/-- The entries of `act A ψ` are those of `A *ᵥ ψ`. -/
theorem act_apply_apply (A : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) (i : m) :
    act A ψ i = (A *ᵥ ψ.ofLp) i :=
  rfl

/-- `act A` on a standard basis vector is the corresponding column of `A`. -/
theorem act_single_apply [DecidableEq n] (A : Matrix m n ℂ) (j : n) (i : m) :
    act A (EuclideanSpace.single j (1 : ℂ)) i = A i j := by
  rw [act_apply_apply, PiLp.ofLp_single, Matrix.mulVec_single_one]
  rfl

/-- The operator norm of `act A` is the operator norm of `A`. -/
theorem norm_act [DecidableEq n] (A : Matrix m n ℂ) : ‖act A‖ = ‖A‖ :=
  rfl

/-- `act` turns matrix products into composition. -/
theorem act_mul [Fintype l] (A : Matrix m n ℂ) (B : Matrix n l ℂ) (ψ : EuclideanSpace ℂ l) :
    act (A * B) ψ = act A (act B ψ) := by
  simp [act_apply, Matrix.mulVec_mulVec]

end TNLean.PEPS.EncodedFrame
