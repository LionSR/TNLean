/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.Algebra.NewtonGirard
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Data.Matrix.Basic

/-!
# Scalar Power-Sum Identity

This file proves that if two families of complex scalars indexed by the same
finite type have equal power sums for all positive exponents, then their
diagonal matrices have equal characteristic polynomials, and consequently the
two families give rise to the same multiset of values.

This is the content of **Lemma Lem:app_simple** of arXiv:1606.00608 (lines
1155–1163).

## Strategy

We reduce to the already-proved `Matrix.charpoly_eq_of_forall_trace_pow_eq`
from `MPSLean.PiAlgebra.NewtonGirard` by observing that the trace of a power
of a diagonal matrix equals the corresponding power sum:

  `trace (diagonal a ^ k) = ∑ i, a i ^ k`

## Main results

* `Matrix.trace_diagonal_pow`: `trace (diagonal a ^ k) = ∑ i, a i ^ k`.

* `Matrix.sum_pow_eq_implies_charpoly_diagonal_eq`: If `∑ i, a i ^ k = ∑ i, b i ^ k`
  for all `k ≥ 1`, then `(diagonal a).charpoly = (diagonal b).charpoly`.

* `Matrix.sum_pow_eq_implies_multiset_eq`: Under the same hypotheses, the multisets
  `Finset.univ.val.map a` and `Finset.univ.val.map b` are equal.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.unusedDecidableInType false

open scoped Matrix BigOperators
open Polynomial Finset Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace of a power of a diagonal matrix equals the power sum of the entries. -/
theorem trace_diagonal_pow (a : n → ℂ) (k : ℕ) :
    trace (diagonal a ^ k) = ∑ i, a i ^ k := by
  rw [diagonal_pow, trace_diagonal]
  exact Finset.sum_congr rfl (fun i _ => Pi.pow_apply a k i)

/-- **Scalar power-sum identity** (Lemma Lem:app_simple of arXiv:1606.00608).

If two families of complex scalars, indexed by the same finite type, have equal
power sums for all positive exponents, then their characteristic polynomials
(as diagonal matrices) agree. -/
theorem sum_pow_eq_implies_charpoly_diagonal_eq
    (a b : n → ℂ)
    (h : ∀ k : ℕ, 0 < k → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    (diagonal a).charpoly = (diagonal b).charpoly := by
  apply charpoly_eq_of_forall_trace_pow_eq
  intro k hk
  rw [trace_diagonal_pow, trace_diagonal_pow]
  exact h k hk

/-- Equal power sums of two families indexed by the same type imply that the
families give rise to the same multiset of values.

This is a direct corollary: equal charpolys of diagonal matrices unfold
(via `charpoly_diagonal`) to `∏ i, (X - C (a i)) = ∏ i, (X - C (b i))`,
from which we extract equal roots. -/
theorem sum_pow_eq_implies_multiset_eq
    (a b : n → ℂ)
    (h : ∀ k : ℕ, 0 < k → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    Finset.univ.val.map a = Finset.univ.val.map b := by
  have hcp := sum_pow_eq_implies_charpoly_diagonal_eq a b h
  rw [charpoly_diagonal, charpoly_diagonal] at hcp
  -- Both sides are equal as polynomials; extract roots
  have : (∏ i : n, (X - C (a i))).roots = (∏ i : n, (X - C (b i))).roots :=
    congrArg Polynomial.roots hcp
  -- Compute roots of ∏ i, (X - C (f i)) using roots_prod
  have roots_eq (f : n → ℂ) : (∏ i : n, (X - C (f i))).roots = Finset.univ.val.map f := by
    have hne : ∏ i : n, (X - C (f i)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      exact fun i _ => X_sub_C_ne_zero (f i)
    rw [roots_prod _ _ hne]
    simp [roots_X_sub_C, Multiset.bind_singleton]
  rwa [roots_eq a, roots_eq b] at this

end Matrix
