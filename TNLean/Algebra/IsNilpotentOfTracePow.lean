/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import QICLean.Algebra.ShiftedZeroTraceNilpotent

/-!
# Nilpotency from vanishing traces of positive powers

This file shows that an endomorphism of a finite-dimensional complex vector space, all of whose
positive powers have vanishing trace, is nilpotent.

The matrix statement is `Matrix.isNilpotent_of_forall_trace_pow_eq_zero_of_one_lt` from
`QICLean.Algebra.ShiftedZeroTraceNilpotent`, which needs vanishing traces only for the exponents
above one. Transporting it through the matrix representation attached to a basis gives the
statement for endomorphisms.

## Main results

* `LinearMap.isNilpotent_of_forall_trace_pow_eq_zero`: an endomorphism of a finite-dimensional
  complex vector space with `trace (f ^ k) = 0` for every `k > 0` is nilpotent.
-/

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- An endomorphism of a finite-dimensional complex vector space, all of whose positive powers
have vanishing trace, is nilpotent.

Transported from `Matrix.isNilpotent_of_forall_trace_pow_eq_zero_of_one_lt` through the algebra
equivalence `LinearMap.toMatrixAlgEquiv` associated with a basis. -/
theorem isNilpotent_of_forall_trace_pow_eq_zero (f : Module.End ℂ V)
    (h : ∀ k : ℕ, 0 < k → LinearMap.trace ℂ V (f ^ k) = 0) : IsNilpotent f := by
  classical
  let b := Module.finBasis ℂ V
  let e := LinearMap.toMatrixAlgEquiv b
  have htr : ∀ g : Module.End ℂ V, LinearMap.trace ℂ V g = Matrix.trace (e g) := fun g =>
    LinearMap.trace_eq_matrix_trace ℂ b g
  have hpow : ∀ k : ℕ, e (f ^ k) = e f ^ k := fun k => map_pow e f k
  have hM : ∀ k : ℕ, 1 < k → Matrix.trace (e f ^ k) = 0 := by
    intro k hk
    rw [← hpow k, ← htr]
    exact h k (by omega)
  obtain ⟨m, hm⟩ :=
    Matrix.isNilpotent_of_forall_trace_pow_eq_zero_of_one_lt (e f) hM
  refine ⟨m, e.injective ?_⟩
  rw [hpow m, hm, map_zero]

end LinearMap
