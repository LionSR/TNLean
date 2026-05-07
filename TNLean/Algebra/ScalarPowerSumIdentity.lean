/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.NewtonGirard
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Scalar Power-Sum Identity

This file provides a **same-cardinality, all-positive-power corollary** used as a support lemma
for the Appendix argument of arXiv:1606.00608.  It is *not* the exact statement of Lemma
`Lem:app_simple` (lines 1155–1163 of the paper), which treats two sorted families of complex
numbers with **possibly different cardinalities** and only requires equality up to
`N ≤ max{x_a, x_b}`.  See the design note below for what would be needed to formalize the
precise lemma.

Given two families of `n` complex scalars whose power sums agree for all positive exponents,
Newton's identities imply their diagonal matrices have equal characteristic polynomials, and
hence the families give the same multiset of values (counted with multiplicity).  This is the
version used throughout the coefficient-comparison and weight-recovery arguments in
`SectorWeightComparison` and `EqualProportional`.

## Strategy

We reduce to the already-proved `Matrix.charpoly_eq_of_forall_trace_pow_eq` from
`TNLean.Algebra.NewtonGirard` by observing that the trace of a power of a diagonal matrix equals
the corresponding power sum:

  `trace (diagonal a ^ k) = ∑ i, a i ^ k`

## Main results

* `Matrix.trace_diagonal_pow`: `trace (diagonal a ^ k) = ∑ i, a i ^ k`.

* `Matrix.sum_pow_eq_implies_charpoly_diagonal_eq`: If `∑ i, a i ^ k = ∑ i, b i ^ k` for all
  `k ≥ 1`, then `(diagonal a).charpoly = (diagonal b).charpoly`.

* `Matrix.sum_pow_eq_implies_multiset_eq`: Under the same hypotheses, the multisets
  `Finset.univ.val.map a` and `Finset.univ.val.map b` are equal.

## Design note: missing exact source statement

The paper's Lemma `Lem:app_simple` (arXiv:1606.00608, lines 1155–1163) states:

  Let `λ_{a,k}` (k=1,…,x_a) and `λ_{b,k}` (k=1,…,x_b) be two **sorted** finite families
  of complex numbers (sorted by nonincreasing absolute value, then nondecreasing argument).
  If `∀ N ≤ max{x_a, x_b}`,
    `∑_{k=1}^{x_a} λ_{a,k}^N = ∑_{k=1}^{x_b} λ_{b,k}^N`,
  then `x_a = x_b` and `λ_{a,k} = λ_{b,k}` for all k.

The formalized version in this file differs in three ways:

  1. **Same cardinality**: both families share the same finite type `n` (no deduction of
     `x_a = x_b`).
  2. **Unbounded exponent range**: equality is for *all* `k > 0`, not just `k ≤ max{x_a, x_b}`.
  3. **No sorting hypothesis**: we work directly with multisets through the characteristic
     polynomial, making lexicographic-phase sorting unnecessary — the polynomial equality
     absorbs the ordering.

These relaxations suffice for the coefficient-comparison path taken in the formalized
fundamental theorems (where the two families are already known to have the same length).
A full formalization of `Lem:app_simple` as written would require:
  - a "sorted complex list" type with the paper's sorting convention,
  - powers up to the larger cardinality,
  - a combinatorial counting-via-Vandermonde proof to conclude cardinality equality.
-/

open scoped Matrix BigOperators

open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace of a power of a diagonal matrix equals the power sum of the entries. -/
theorem trace_diagonal_pow (a : n → ℂ) (k : ℕ) :
    trace (diagonal a ^ k) = ∑ i, a i ^ k := by
  simp [diagonal_pow, trace_diagonal]

/-- **Scalar power-sum identity** (same-cardinality support lemma for
`Lem:app_simple` of arXiv:1606.00608).

If two families of complex scalars, indexed by the same finite type, have equal power sums for all
positive exponents, then their characteristic polynomials (as diagonal matrices) agree. -/
theorem sum_pow_eq_implies_charpoly_diagonal_eq
    (a b : n → ℂ)
    (h : ∀ k : ℕ, 0 < k → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    (diagonal a).charpoly = (diagonal b).charpoly := by
  apply charpoly_eq_of_forall_trace_pow_eq
  intro k hk
  rw [trace_diagonal_pow, trace_diagonal_pow]
  exact h k hk

-- `DecidableEq n` is only needed to define diagonal matrices in the proof, not in the statement.
set_option linter.unusedDecidableInType false in
/-- Equal power sums of two families indexed by the same finite type imply that the families
give rise to the same multiset of values.

This is a direct corollary: equal characteristic polynomials of diagonal matrices unfold (via
`charpoly_diagonal`) to `∏ i, (X - C (a i)) = ∏ i, (X - C (b i))`, from which we extract equal
roots.  Note that this is a **same-cardinality** result; the paper's `Lem:app_simple` additionally
deduces cardinality equality when the sizes may differ. -/
theorem sum_pow_eq_implies_multiset_eq
    (a b : n → ℂ)
    (h : ∀ k : ℕ, 0 < k → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    Finset.univ.val.map a = Finset.univ.val.map b := by
  have hcp := sum_pow_eq_implies_charpoly_diagonal_eq a b h
  rw [charpoly_diagonal, charpoly_diagonal] at hcp
  have hroots : (∏ i : n, (X - C (a i))).roots = (∏ i : n, (X - C (b i))).roots :=
    congrArg Polynomial.roots hcp
  have roots_eq (f : n → ℂ) : (∏ i : n, (X - C (f i))).roots = Finset.univ.val.map f := by
    have hne : (∏ i : n, (X - C (f i))) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      exact fun i _ => X_sub_C_ne_zero (f i)
    rw [roots_prod _ _ hne]
    simp
  simpa [roots_eq] using hroots

end Matrix
