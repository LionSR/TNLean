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

This is the matrix-algebraic core of the observation in arXiv:1703.09188
(Cirac--Perez-Garcia--Schuch--Verstraete), Proposition `prop:normal-tensor`,
lines 349–354: the transfer-matrix spectrum of a matrix-product unitary
contains a single eigenvalue equal to one and all others vanish.  The
paper's proof route uses Lemma A.5 of arXiv:1606.00608; we formalize it
via Newton--Girard identities as already developed in
`TNLean.Algebra.NewtonGirard`, comparing against an explicit rank-one
idempotent whose positive powers all have trace one.

The proof is purely algebraic: no spectral radius, positivity, normality, or
diagonalizability is required.  A companion paper-gap note
`docs/paper-gaps/cpsv17_transfer_trace_power.tex` records the scope
restriction to `Fintype.card n ≥ 1` (the source assumes a transfer matrix
of a unitary tensor, which always has positive dimension).

## Main results

* `Matrix.charpoly_eq_X_pow_pred_mul_X_sub_one_of_trace_pow_eq_one_of_le_card`:
  finite-range version: if `tr(A^k) = 1` for `1 ≤ k ≤ card n` and
  `0 < Fintype.card n`, then
  `A.charpoly = X ^ (Fintype.card n - 1) * (X - 1)`.

* `Matrix.charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one`:
  all-positive-powers corollary.

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
`1 ≤ k ≤ card n`, then `A.charpoly = X^(n-1) * (X-1)`.  In particular `A`
has a single nonzero eigenvalue equal to one, with the rest equal to zero.

This is the algebraic core of the observation in arXiv:1703.09188
(Cirac--Perez-Garcia--Schuch--Verstraete), Proposition `prop:normal-tensor`,
lines 349–354.

**Scope restriction:** The dimension `Fintype.card n` must be positive
(`0 < Fintype.card n`).  In the source context `A` is the transfer matrix
of a unitary tensor, whose index type always has at least one element.
The restriction is recorded in
`docs/paper-gaps/cpsv17_transfer_trace_power.tex`. -/
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

This is the corollary of the finite-range version obtained by restricting
its hypothesis to `1 ≤ k ≤ card n`.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 349–354. -/
theorem charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one
    (A : Matrix n n ℂ)
    (hcard : 0 < Fintype.card n)
    (h : ∀ k : ℕ, 0 < k → trace (A ^ k) = 1) :
    A.charpoly = X ^ (Fintype.card n - 1) * (X - 1) :=
  charpoly_eq_X_pow_pred_mul_X_sub_one_of_trace_pow_eq_one_of_le_card A hcard
    (fun k hk _ => h k hk)

end Matrix
