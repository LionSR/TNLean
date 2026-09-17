/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import QICLean.Algebra.NewtonGirard

/-!
# Nilpotency from vanishing traces of positive powers

This file shows that a complex matrix, or an endomorphism of a finite-dimensional complex
vector space, all of whose positive powers have vanishing trace, is nilpotent.

The comparison of characteristic polynomials via matching trace power sums is the
Newton–Girard step `Matrix.charpoly_eq_of_forall_trace_pow_eq` from
`QICLean.Algebra.NewtonGirard`.
Comparing against the zero matrix identifies the characteristic polynomial with `X ^ card n`, and
Cayley–Hamilton then gives nilpotency directly.

## Main results

* `Matrix.isNilpotent_of_forall_trace_pow_eq_zero`: a complex square matrix with
  `trace (M ^ k) = 0` for every `k > 0` is nilpotent.
* `LinearMap.isNilpotent_of_forall_trace_pow_eq_zero`: the same statement for an endomorphism of
  a finite-dimensional complex vector space, obtained by transporting through a basis.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complex square matrix all of whose positive powers have vanishing trace is nilpotent.

The characteristic polynomial of `M` agrees with that of the zero matrix, `X ^ card n`, by
matching trace-power sums (`Matrix.charpoly_eq_of_forall_trace_pow_eq`); Cayley–Hamilton then
gives `M ^ card n = 0`. -/
theorem isNilpotent_of_forall_trace_pow_eq_zero (M : Matrix n n ℂ)
    (h : ∀ k : ℕ, 0 < k → Matrix.trace (M ^ k) = 0) : IsNilpotent M := by
  have htrace : ∀ k : ℕ, 0 < k →
      Matrix.trace (M ^ k) = Matrix.trace ((0 : Matrix n n ℂ) ^ k) := by
    intro k hk
    rw [h k hk, zero_pow hk.ne', Matrix.trace_zero]
  have hchar : M.charpoly = (0 : Matrix n n ℂ).charpoly :=
    Matrix.charpoly_eq_of_forall_trace_pow_eq M 0 htrace
  rw [Matrix.charpoly_zero] at hchar
  refine ⟨Fintype.card n, ?_⟩
  have hcayley := Matrix.aeval_self_charpoly M
  rwa [hchar, map_pow, Polynomial.aeval_X] at hcayley

end Matrix

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- An endomorphism of a finite-dimensional complex vector space, all of whose positive powers
have vanishing trace, is nilpotent.

Transported from `Matrix.isNilpotent_of_forall_trace_pow_eq_zero` through the algebra
equivalence `LinearMap.toMatrixAlgEquiv` associated with a basis. -/
theorem isNilpotent_of_forall_trace_pow_eq_zero (f : Module.End ℂ V)
    (h : ∀ k : ℕ, 0 < k → LinearMap.trace ℂ V (f ^ k) = 0) : IsNilpotent f := by
  classical
  let b := Module.finBasis ℂ V
  let e := LinearMap.toMatrixAlgEquiv b
  have htr : ∀ g : Module.End ℂ V, LinearMap.trace ℂ V g = Matrix.trace (e g) := fun g =>
    LinearMap.trace_eq_matrix_trace ℂ b g
  have hpow : ∀ k : ℕ, e (f ^ k) = e f ^ k := fun k => map_pow e f k
  have hM : ∀ k : ℕ, 0 < k → Matrix.trace (e f ^ k) = 0 := by
    intro k hk
    rw [← hpow k, ← htr]
    exact h k hk
  obtain ⟨m, hm⟩ := Matrix.isNilpotent_of_forall_trace_pow_eq_zero (e f) hM
  refine ⟨m, e.injective ?_⟩
  rw [hpow m, hm, map_zero]

end LinearMap
