/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.NewtonGirard
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Trace-Power Lemma: All Positive Traces Equal to One

Suppose `A` is an `n × n` matrix over `ℂ` such that `tr(A^k) = 1` for all
`k ≥ 1`.  Then `A.charpoly = X^(n-1) * (X - 1)`.  In particular `A` has a
single nonzero eigenvalue equal to one, with the rest equal to zero.

This is a Newton--Girard prerequisite for the transfer-matrix spectrum
argument in arXiv:1703.09188 (Cirac--Perez-Garcia--Schuch--Verstraete),
Proposition `prop:normal-tensor`, lines 349–354.  The present file proves this statement for the stronger hypothesis
`tr(A^k) = 1` for all `k ≥ 1` (the Newton--Girard prerequisite).
The paper's exact `N > 1` hypothesis is handled by the companion formalization, which does
**not** recover `tr(E) = 1`; it proves directly that the nonzero spectrum
equals `{1}` without computing the first moment.  The bridge between the
two results is documented in `docs/paper-gaps/cpsv17_transfer_trace_power.tex`.

The proof is purely algebraic: no spectral radius, positivity, normality, or
diagonalizability is required.  We construct an explicit rank-one diagonal
idempotent whose positive powers all have trace one, then invoke the
Newton--Girard lemma `Matrix.charpoly_eq_of_trace_pow_eq_of_le_card` from
`TNLean.Algebra.NewtonGirard`.

## Main results

* `Matrix.charpoly_eq_X_pow_pred_mul_X_sub_one_of_trace_pow_eq_one_of_le_card`:
  finite-range version: if `tr(A^k) = 1` for `1 ≤ k ≤ card n` and
  `0 < Fintype.card n`, then
  `A.charpoly = X ^ (Fintype.card n - 1) * (X - 1)`.

* `Matrix.charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one`:
  all-positive-powers theorem: if `tr(A^k) = 1` for all `k ≥ 1`, same
  conclusion.  The positive-cardinality condition is derived internally
  from `h 1` (the empty-index case is contradictory).

## Proof strategy

1. Build a *reference* rank-one idempotent `diagonalOneAt i0` (a diagonal
   matrix with a single `1` at position `i0`).  For `k ≥ 1`:
   `(diagonalOneAt i0)^k = diagonalOneAt i0`, so `trace = 1`.

2. Its characteristic polynomial is `X^(n-1) * (X-1)` by the formula
   `charpoly (diagonal d) = ∏ i, (X - C (d i))`.

3. Compare `A` with the reference matrix using the Newton--Girard lemma
   `Matrix.charpoly_eq_of_trace_pow_eq_of_le_card` from
   `TNLean.Algebra.NewtonGirard`: equality of traces through `card n`
   forces equality of characteristic polynomials.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1703.09188,
  Proposition `prop:normal-tensor`, lines 349–354
* [Cirac--Perez-Garcia--Schuch--Verstraete 2016] arXiv:1606.00608,
  Lemma A.5, lines 1155–1163 (scalar power-sum identity)

## Tags

trace, characteristic polynomial, Newton-Girard, matrix product unitary,
transfer matrix
-/

open scoped Matrix BigOperators
open Polynomial Finset Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Reference rank-one idempotent -/

/-- A diagonal matrix with a single `1` at `i0` and zeros elsewhere.
Its positive powers are idempotent: `M^k = M` for `k ≥ 1`. -/
def diagonalOneAt (i0 : n) : Matrix n n ℂ :=
  diagonal (fun i => if i = i0 then 1 else 0)

@[simp]
lemma trace_diagonalOneAt (i0 : n) : trace (diagonalOneAt i0) = 1 := by
  simp [diagonalOneAt, trace_diagonal]

/-- Positive powers of a rank-one diagonal idempotent are the matrix itself. -/
lemma diagonalOneAt_pow (i0 : n) (k : ℕ) (hk : 0 < k) :
    (diagonalOneAt i0) ^ k = diagonalOneAt i0 := by
  rw [diagonalOneAt, diagonal_pow]
  congr
  ext i
  by_cases h : i = i0
  · subst i; simp
  · simp [h, hk.ne']

lemma trace_pow_diagonalOneAt (i0 : n) (k : ℕ) (hk : 0 < k) :
    trace ((diagonalOneAt i0) ^ k) = 1 := by
  rw [diagonalOneAt_pow i0 k hk, trace_diagonalOneAt]

/-- The characteristic polynomial of a rank-one diagonal idempotent is
`X^(n-1) * (X-1)`: one eigenvalue `1` and `n-1` eigenvalues `0`. -/
lemma charpoly_diagonalOneAt (i0 : n) :
    (diagonalOneAt i0).charpoly = X ^ (Fintype.card n - 1) * (X - 1) := by
  rw [diagonalOneAt, charpoly_diagonal]
  have hcard_erase : Finset.card ((Finset.univ : Finset n).erase i0) = Fintype.card n - 1 := by
    calc
      Finset.card ((Finset.univ : Finset n).erase i0) =
          Finset.card (Finset.univ : Finset n) - 1 :=
        Finset.card_erase_of_mem (Finset.mem_univ i0)
      _ = Fintype.card n - 1 := by simp
  have hfirst : (X - C (if i0 = i0 then (1 : ℂ) else 0)) = (X - 1) := by simp
  have hrest : (∏ x ∈ ((Finset.univ : Finset n).erase i0),
      (X - C (if x = i0 then (1 : ℂ) else 0))) = X ^ (Fintype.card n - 1) := by
    -- For x ≠ i0, the if-condition is false, so the factor is X - C 0 = X
    have hprod_congr : (∏ x ∈ ((Finset.univ : Finset n).erase i0),
        (X - C (if x = i0 then (1 : ℂ) else 0))) =
        (∏ x ∈ ((Finset.univ : Finset n).erase i0), X) :=
      Finset.prod_congr rfl (fun x hx => by
        have hx_ne : x ≠ i0 := (Finset.mem_erase.mp hx).1
        simp [hx_ne])
    rw [hprod_congr]
    simp [hcard_erase]
  -- Factor out the i0 term from the full product
  have hprod_split : (∏ i, (X - C (if i = i0 then (1 : ℂ) else 0))) =
      (X - C (if i0 = i0 then (1 : ℂ) else 0)) *
      (∏ x ∈ ((Finset.univ : Finset n).erase i0),
        (X - C (if x = i0 then (1 : ℂ) else 0))) := by
    have h := Finset.prod_erase_mul (Finset.univ : Finset n)
      (fun i => X - C (if i = i0 then (1 : ℂ) else 0)) (Finset.mem_univ i0)
    -- h : (∏ erase) * (f i0) = ∏ total
    -- Goal: ∏ total = (f i0) * (∏ erase)
    rw [h.symm, mul_comm]
  calc
    ∏ i, (X - C (if i = i0 then (1 : ℂ) else 0))
        = (X - C (if i0 = i0 then (1 : ℂ) else 0)) *
          (∏ x ∈ ((Finset.univ : Finset n).erase i0),
            (X - C (if x = i0 then (1 : ℂ) else 0))) := hprod_split
    _ = (X - 1) *
        (∏ x ∈ ((Finset.univ : Finset n).erase i0),
          (X - C (if x = i0 then (1 : ℂ) else 0))) := by rw [hfirst]
    _ = (X - 1) * (X ^ (Fintype.card n - 1)) := by rw [hrest]
    _ = X ^ (Fintype.card n - 1) * (X - 1) := by ring

/-! ### Main theorems -/

/-- **Finite-range trace-power lemma.**

If an `n × n` complex matrix `A` satisfies `tr(A^k) = 1` for
`1 ≤ k ≤ card n` and `0 < Fintype.card n`, then
`A.charpoly = X^(n-1) * (X-1)`.  In particular `A` has a single nonzero
eigenvalue equal to one, with the rest equal to zero.

The positive-cardinality hypothesis `0 < Fintype.card n` is required here
because the finite-range hypothesis is vacuous when `card n = 0` (there are
no `k` with `0 < k ≤ 0`), so the theorem cannot extract a witness.  The
all-positive-powers corollary below derives the cardinality condition
internally. -/
theorem charpoly_eq_X_pow_pred_mul_X_sub_one_of_trace_pow_eq_one_of_le_card
    (A : Matrix n n ℂ)
    (hcard : 0 < Fintype.card n)
    (h : ∀ k : ℕ, 0 < k → k ≤ Fintype.card n → trace (A ^ k) = 1) :
    A.charpoly = X ^ (Fintype.card n - 1) * (X - 1) := by
  -- `hcard` guarantees the index type is nonempty, so we can pick an `i0`
  have hne : Nonempty n := Fintype.card_pos_iff.mp hcard
  let i0 : n := Classical.choice hne
  have htrace_ref (k : ℕ) (hk : 0 < k) (_hkcard : k ≤ Fintype.card n) :
      trace ((diagonalOneAt i0) ^ k) = 1 :=
    trace_pow_diagonalOneAt i0 k hk
  -- Compare `A` with the reference matrix via Newton--Girard
  have hcharpoly_eq : A.charpoly = (diagonalOneAt i0).charpoly :=
    charpoly_eq_of_trace_pow_eq_of_le_card A (diagonalOneAt i0)
      (fun k hk hkcard => by
        rw [h k hk hkcard, htrace_ref k hk hkcard])
  rw [hcharpoly_eq, charpoly_diagonalOneAt i0]

/-- **All-positive-powers trace-power lemma.**

If `tr(A^k) = 1` for all `k ≥ 1`, then
`A.charpoly = X^(n-1) * (X-1)`.

In particular `A` has a single nonzero eigenvalue equal to one, with the
rest equal to zero.  The positive-cardinality condition is derived
internally from the first-moment hypothesis `tr(A) = 1` (when the index
type is empty, the trace is `0`, contradicting the hypothesis).

This is a Newton--Girard prerequisite for the transfer-matrix spectrum
argument in arXiv:1703.09188, Proposition `prop:normal-tensor`, lines
349–354.  The paper supplies `tr(E^N) = 1` for `N > 1` from unitarity of
blocked tensors.  The present theorem uses the stronger hypothesis
`tr(A^k) = 1` for all `k ≥ 1`; the paper's exact `N > 1` hypothesis is
handled by the companion formalization, which proves the nonzero spectrum is `{1}` without
recovering `tr(E) = 1`.  See `docs/paper-gaps/cpsv17_transfer_trace_power.tex`. -/
theorem charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 0 < k → trace (A ^ k) = 1) :
    A.charpoly = X ^ (Fintype.card n - 1) * (X - 1) := by
  by_cases hcard0 : Fintype.card n = 0
  · -- Empty index type: `trace (A ^ 1) = 1` contradicts `trace = 0`
    haveI : IsEmpty n := (Fintype.card_eq_zero_iff.mp hcard0)
    have htrace0 : trace (A ^ 1) = 0 := by
      simp [trace]
    have htrace1 := h 1 (by norm_num)
    rw [htrace1] at htrace0
    exact absurd htrace0 one_ne_zero
  · -- Positive cardinality: delegate to the finite-range theorem
    have hcard_pos : 0 < Fintype.card n := Nat.pos_of_ne_zero hcard0
    exact charpoly_eq_X_pow_pred_mul_X_sub_one_of_trace_pow_eq_one_of_le_card A hcard_pos
      (fun k hk _ => h k hk)

end Matrix
