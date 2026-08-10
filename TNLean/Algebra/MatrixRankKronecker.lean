/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.RingTheory.Flat.Basic

/-!
# Rank of a Kronecker product

This file proves that matrix rank is multiplicative under the Kronecker product over a field.

## Main result

* `Matrix.rank_kronecker`: the rank of `A ⊗ₖ B` is the product of the ranks of `A` and `B`.
-/

open Module
open scoped Kronecker

namespace Matrix

variable {K m n p q : Type*} [Field K] [Finite m] [Fintype n] [Finite p] [Fintype q]

/-- Matrix rank is multiplicative under the Kronecker product over a field. -/
theorem rank_kronecker (A : Matrix m n K) (B : Matrix p q K) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  classical
  rw [Matrix.rank_eq_finrank_range_toLin (A ⊗ₖ B)
      ((Pi.basisFun K m).tensorProduct (Pi.basisFun K p))
      ((Pi.basisFun K n).tensorProduct (Pi.basisFun K q)),
    Matrix.toLin_kronecker,
    TensorProduct.range_map,
    ← TensorProduct.range_mapIncl,
    LinearMap.finrank_range_of_inj
      (Module.Flat.tensorProduct_mapIncl_injective_of_left
        (LinearMap.range (Matrix.toLin (Pi.basisFun K n) (Pi.basisFun K m) A))
        (LinearMap.range (Matrix.toLin (Pi.basisFun K q) (Pi.basisFun K p) B))),
    Module.finrank_tensorProduct,
    ← Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun K m) (Pi.basisFun K n),
    ← Matrix.rank_eq_finrank_range_toLin B (Pi.basisFun K p) (Pi.basisFun K q)]

end Matrix
