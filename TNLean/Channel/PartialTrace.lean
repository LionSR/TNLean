/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic

/-!
# Partial trace on bipartite matrices

This file defines partial traces for matrices indexed by product types,
as needed for the Choi–Jamiolkowski isomorphism (Wolf Ch. 2, Prop 2.1).

## Main definitions

* `Matrix.traceLeft` (`tr_A`): trace over the first (left) tensor factor
* `Matrix.traceRight` (`tr_B`): trace over the second (right) tensor factor

## Main results

* `Matrix.traceLeft_apply`: elementwise formula for `tr_A`
* `Matrix.traceRight_apply`: elementwise formula for `tr_B`
* `Matrix.trace_eq_trace_traceLeft`: `tr(X) = tr(tr_A(X))`
* `Matrix.trace_eq_trace_traceRight`: `tr(X) = tr(tr_B(X))`
* `Matrix.traceLeft_kronecker`: `tr_A(A ⊗ B) = tr(A) • B`
* `Matrix.traceRight_kronecker`: `tr_B(A ⊗ B) = A • tr(B)`
* `Matrix.traceLeft_one`: `tr_A(1) = d • 1`
* `Matrix.traceRight_one`: `tr_B(1) = d' • 1`

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2][Wolf2012QChannels]
-/

open scoped Matrix
open Matrix Finset BigOperators

namespace Matrix

variable {d d' : ℕ}

/-- **Partial trace over the first (left) tensor factor** (`tr_A`).

For a matrix `X : M_{d·d'}(ℂ)` indexed by `(Fin d × Fin d')`, the partial
trace over the first factor produces a `d' × d'` matrix:

  `(traceLeft X) i j = ∑ k, X (k, i) (k, j)` -/
noncomputable def traceLeft (X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    Matrix (Fin d') (Fin d') ℂ :=
  fun i j => ∑ k : Fin d, X (k, i) (k, j)

/-- **Partial trace over the second (right) tensor factor** (`tr_B`).

For a matrix `X : M_{d·d'}(ℂ)` indexed by `(Fin d × Fin d')`, the partial
trace over the second factor produces a `d × d` matrix:

  `(traceRight X) i j = ∑ k, X (i, k) (j, k)` -/
noncomputable def traceRight (X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => ∑ k : Fin d', X (i, k) (j, k)

@[simp]
theorem traceLeft_apply (X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) (i j : Fin d') :
    traceLeft X i j = ∑ k : Fin d, X (k, i) (k, j) := rfl

@[simp]
theorem traceRight_apply (X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) (i j : Fin d) :
    traceRight X i j = ∑ k : Fin d', X (i, k) (j, k) := rfl

/-- The full trace equals the trace of the left partial trace: `tr(X) = tr(tr_A(X))`. -/
theorem trace_eq_trace_traceLeft (X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    X.trace = (traceLeft X).trace := by
  simp only [Matrix.trace, Matrix.diag, traceLeft_apply]
  rw [show ∑ i : Fin d × Fin d', X i i =
    ∑ k : Fin d, ∑ j : Fin d', X (k, j) (k, j) from Fintype.sum_prod_type _]
  exact Finset.sum_comm

/-- The full trace equals the trace of the right partial trace: `tr(X) = tr(tr_B(X))`. -/
theorem trace_eq_trace_traceRight (X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    X.trace = (traceRight X).trace := by
  simp only [Matrix.trace, Matrix.diag, traceRight_apply]
  exact Fintype.sum_prod_type _

/-- `traceLeft` is additive. -/
theorem traceLeft_add (X Y : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    traceLeft (X + Y) = traceLeft X + traceLeft Y := by
  ext i j; simp [traceLeft_apply, Finset.sum_add_distrib]

/-- `traceLeft` commutes with scalar multiplication. -/
theorem traceLeft_smul (c : ℂ) (X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    traceLeft (c • X) = c • traceLeft X := by
  ext i j; simp [traceLeft_apply, Finset.mul_sum]

/-- `traceRight` is additive. -/
theorem traceRight_add (X Y : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    traceRight (X + Y) = traceRight X + traceRight Y := by
  ext i j; simp [traceRight_apply, Finset.sum_add_distrib]

/-- `traceRight` commutes with scalar multiplication. -/
theorem traceRight_smul (c : ℂ) (X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    traceRight (c • X) = c • traceRight X := by
  ext i j; simp [traceRight_apply, Finset.mul_sum]

/-- `traceLeft` as a linear map. -/
noncomputable def traceLeftLM (d d' : ℕ) :
    Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ where
  toFun := traceLeft
  map_add' := traceLeft_add
  map_smul' := traceLeft_smul

/-- `traceRight` as a linear map. -/
noncomputable def traceRightLM (d d' : ℕ) :
    Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun := traceRight
  map_add' := traceRight_add
  map_smul' := traceRight_smul

/-- Left partial trace of a Kronecker product: `tr_A(A ⊗ B) = tr(A) • B`. -/
theorem traceLeft_kronecker (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d') (Fin d') ℂ) :
    traceLeft (kroneckerMap (· * ·) A B) = A.trace • B := by
  ext i j
  simp only [traceLeft_apply, kroneckerMap_apply, Matrix.smul_apply, Matrix.trace,
    Matrix.diag, smul_eq_mul, Finset.sum_mul]

/-- Right partial trace of a Kronecker product: `tr_B(A ⊗ B) = tr(B) • A`. -/
theorem traceRight_kronecker (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d') (Fin d') ℂ) :
    traceRight (kroneckerMap (· * ·) A B) = B.trace • A := by
  ext i j
  simp only [traceRight_apply, kroneckerMap_apply, Matrix.smul_apply, Matrix.trace,
    Matrix.diag, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- `traceLeft` of the identity is `(d : ℂ) • 1`. -/
theorem traceLeft_one :
    traceLeft (1 : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) = (d : ℂ) • 1 := by
  ext i j
  simp only [traceLeft_apply, Matrix.one_apply, Prod.mk.injEq, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · simp [hij]

/-- `traceRight` of the identity is `(d' : ℂ) • 1`. -/
theorem traceRight_one :
    traceRight (1 : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) = (d' : ℂ) • 1 := by
  ext i j
  simp only [traceRight_apply, Matrix.one_apply, Prod.mk.injEq, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · simp [hij]

end Matrix
