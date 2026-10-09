/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank from a factorization and an identity minor

A matrix that factors through a `k`-dimensional space and contains an identity submatrix of size
`k` has rank exactly `k`: the factorization bounds the rank above and the identity minor bounds it
below. This is the shape of the cut-rank computations for explicit matrix product unitaries.
-/

namespace Matrix

variable {R m n k : Type*} [Field R] [Fintype n] [Fintype k] [DecidableEq k]

/-- A matrix `M = A * B` that factors through `k` and has an identity submatrix indexed by `k`
has rank `Fintype.card k`. -/
theorem rank_eq_card_of_eq_mul_of_submatrix_eq_one (M : Matrix m n R) (A : Matrix m k R)
    (B : Matrix k n R) (hM : M = A * B) (r : k → m) (c : k → n)
    (hsub : M.submatrix r c = 1) :
    M.rank = Fintype.card k := by
  refine le_antisymm ?_ ?_
  · rw [hM]
    exact (rank_mul_le_left A B).trans (rank_le_card_width A)
  · have h := rank_submatrix_le M r c
    rwa [hsub, rank_one] at h

end Matrix
