/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Operator-Schmidt rank

This file defines the operator-Schmidt rank of a finite bipartite operator as
the dimension of the range of its reshaped linear map.  The range is proved to
be the span of the operator blocks, giving a basis-free form of the usual
minimum-length product decomposition.

## Main definitions

* `Matrix.operatorBlock`: a block of a bipartite operator.
* `Matrix.operatorSchmidtMap`: the associated reshaped linear map.
* `Matrix.operatorBlockSpan`: the span of all operator blocks.
* `Matrix.operatorSchmidtRank`: the range dimension of the reshaped map.

## Main statements

* `Matrix.range_operatorSchmidtMap_eq_operatorBlockSpan`: the range of the
  reshaped map is exactly the span of the operator blocks.
* `Matrix.operatorSchmidtRank_eq_finrank_operatorBlockSpan`: the
  operator-Schmidt rank is the dimension of that span.

## References

* G. De las Cuevas, T. Drescher, and T. Netzer, arXiv:1903.05373,
  definition of operator-Schmidt rank preceding Theorem 1.
-/

open scoped BigOperators

namespace Matrix

variable {R m n : Type*}

/-- The `(i,j)` operator block of a bipartite matrix, regarded as a matrix on
the second factor.

This is the block family used in the ordinary operator-Schmidt decomposition;
see arXiv:1903.05373, definition preceding Theorem 1. -/
def operatorBlock (ρ : Matrix (m × n) (m × n) R) (i j : m) : Matrix n n R :=
  fun k l ↦ ρ (i, k) (j, l)

section Semiring

variable [Semiring R] [Fintype m]

/-- The reshaped linear map associated with a bipartite operator.  It sends a
coefficient matrix on the first factor to the corresponding linear combination
of operator blocks on the second factor.

Its range dimension is the operator-Schmidt rank of arXiv:1903.05373,
definition preceding Theorem 1. -/
def operatorSchmidtMap (ρ : Matrix (m × n) (m × n) R) :
    Matrix m m R →ₗ[R] Matrix n n R :=
  (Fintype.linearCombination R fun ij : m × m ↦ operatorBlock ρ ij.1 ij.2).comp
    (LinearEquiv.curry R R m m).symm.toLinearMap

@[simp]
theorem operatorSchmidtMap_apply (ρ : Matrix (m × n) (m × n) R)
    (X : Matrix m m R) :
    operatorSchmidtMap ρ X =
      ∑ ij : m × m, X ij.1 ij.2 • operatorBlock ρ ij.1 ij.2 := by
  rfl

/-- The submodule spanned by all operator blocks of a bipartite matrix. -/
def operatorBlockSpan (ρ : Matrix (m × n) (m × n) R) : Submodule R (Matrix n n R) :=
  Submodule.span R (Set.range fun ij : m × m ↦ operatorBlock ρ ij.1 ij.2)

/-- The range of the reshaped map is exactly the span of the operator blocks.

This is the basis-free range formulation of the operator-Schmidt rank used in
arXiv:1903.05373, definition preceding Theorem 1. -/
theorem range_operatorSchmidtMap_eq_operatorBlockSpan
    (ρ : Matrix (m × n) (m × n) R) :
    LinearMap.range (operatorSchmidtMap ρ) = operatorBlockSpan ρ := by
  rw [operatorSchmidtMap, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [Fintype.range_linearCombination]
  rw [operatorBlockSpan]

end Semiring

section Field

variable [Field R] [Fintype m]

/-- The operator-Schmidt rank of a finite bipartite operator, defined without
choosing bases for the local matrix spaces: it is the dimension of the range of
the associated reshaped linear map.

This agrees with the minimum number of elementary tensor factors in
arXiv:1903.05373, definition preceding Theorem 1. -/
noncomputable def operatorSchmidtRank (ρ : Matrix (m × n) (m × n) R) : ℕ :=
  Module.finrank R (LinearMap.range (operatorSchmidtMap ρ))

/-- Operator-Schmidt rank is the dimension of the span of the operator blocks. -/
theorem operatorSchmidtRank_eq_finrank_operatorBlockSpan
    (ρ : Matrix (m × n) (m × n) R) :
    operatorSchmidtRank ρ = Module.finrank R (operatorBlockSpan ρ) := by
  rw [operatorSchmidtRank, range_operatorSchmidtMap_eq_operatorBlockSpan]

end Field

end Matrix
