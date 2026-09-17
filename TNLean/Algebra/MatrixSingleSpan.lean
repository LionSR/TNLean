/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Submodules of matrices containing every matrix unit

A submodule of the matrices over a semiring that contains every matrix unit `E_{ij}` is the
whole space, because every matrix is the sum of its entries times the matrix units. This is the
final step of every normality or injectivity certificate of a worked example: once each matrix
unit has been produced from finitely many words, the span of the words is everything.

## Main results

* `Submodule.eq_top_of_forall_single_mem`: a submodule containing every matrix unit is `⊤`.
-/

namespace Submodule

/-- A submodule of matrices containing every matrix unit `E_{ij}` is the whole space. -/
theorem eq_top_of_forall_single_mem {R m n : Type*} [Semiring R] [Finite m] [Finite n]
    [DecidableEq m] [DecidableEq n] (T : Submodule R (Matrix m n R))
    (h : ∀ i j, Matrix.single i j (1 : R) ∈ T) : T = ⊤ := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  refine top_unique fun X _ => ?_
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using T.smul_mem (X i j) (h i j)

end Submodule
