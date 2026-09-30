/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import QICLean.Algebra.ShiftedZeroTraceNilpotent

/-!
# Matrices whose positive trace powers are constant

A finite complex matrix `N` with `tr(N^k) = c` for every positive exponent `k` has every
eigenvalue equal to `0` or `1`, so that `c = tr N` is the number of eigenvalues equal to `1`,
counted with multiplicity: a nonnegative integer. This is the matrix step of the integrality of
rank-one actions of matrix product operators on normal tensors
(`Notes/OpenProblemsTN/checks/asym_fibonacci_categorical_data.md`, §6.4).

The argument passes through the shifted matrix `N^2 - N`. Expanding a polynomial in `N` shows
that its trace is `p(0)` times the size plus `c` times `p(1) - p(0)`; for `p = (X^2 - X)^k` with
`k ≥ 1` both `p(0)` and `p(1)` vanish, so every positive trace power of `N^2 - N` is zero, its
characteristic polynomial is a power of `X`, and the spectral mapping theorem forces every
eigenvalue `λ` of `N` to satisfy `λ^2 = λ`.

## Main results

* `Matrix.trace_aeval_eq_of_forall_trace_pow_eq`: the trace of a polynomial in `N`.
* `Matrix.exists_nat_eq_of_forall_trace_pow_eq`: the constant value of the trace powers is a
  nonnegative integer.
-/

open Polynomial

/-- A multiset of complex numbers each equal to `0` or `1` sums to a nonnegative integer. -/
theorem Multiset.exists_nat_eq_sum_of_forall_eq_zero_or_one (s : Multiset ℂ)
    (h : ∀ x ∈ s, x = 0 ∨ x = 1) : ∃ m : ℕ, s.sum = m := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons a s ih =>
    obtain ⟨m, hm⟩ := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    rcases h a (Multiset.mem_cons_self a s) with ha | ha
    · exact ⟨m, by simp [ha, hm]⟩
    · exact ⟨m + 1, by simp [ha, hm, add_comm]⟩

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If every positive power of `N` has trace `c`, the trace of a polynomial `p` in `N` is
`p(0)` times the size of `N` plus `c` times `p(1) - p(0)`. -/
theorem trace_aeval_eq_of_forall_trace_pow_eq {N : Matrix n n ℂ} {c : ℂ}
    (h : ∀ k : ℕ, 0 < k → (N ^ k).trace = c) (p : ℂ[X]) :
    (aeval N p).trace = p.coeff 0 * Fintype.card n + c * (p.eval 1 - p.coeff 0) := by
  rw [aeval_eq_sum_range, trace_sum, Finset.sum_range_succ', eval_eq_sum_range,
    Finset.sum_range_succ']
  simp only [trace_smul, smul_eq_mul, pow_zero, trace_one, one_pow, mul_one]
  rw [Finset.sum_congr rfl fun i _ => by rw [h (i + 1) (Nat.succ_pos i)], ← Finset.sum_mul]
  ring

/-- **Constant trace powers are integral.** If `tr(N^k) = c` for every positive `k`, then `c` is
a nonnegative integer: every eigenvalue of `N` is `0` or `1`, and `c = tr N` counts the
eigenvalues equal to `1`. -/
theorem exists_nat_eq_of_forall_trace_pow_eq (N : Matrix n n ℂ) (c : ℂ)
    (h : ∀ k : ℕ, 0 < k → (N ^ k).trace = c) : ∃ m : ℕ, c = m := by
  have hM : ∀ k : ℕ, 0 < k → ((N ^ 2 - N) ^ k).trace = 0 := by
    intro k hk
    have hp : (N ^ 2 - N) ^ k = aeval N (((X : ℂ[X]) ^ 2 - X) ^ k) := by simp
    rw [hp, trace_aeval_eq_of_forall_trace_pow_eq h, coeff_zero_eq_eval_zero]
    simp [hk.ne']
  have hchar := charpoly_eq_X_pow_card_of_forall_trace_pow_eq_zero (N ^ 2 - N) hM
  have hroots : ∀ x ∈ N.charpoly.roots, x = 0 ∨ x = 1 := by
    intro x hx
    have hspec : x ∈ spectrum ℂ N :=
      mem_spectrum_iff_isRoot_charpoly.mpr ((mem_roots N.charpoly_monic.ne_zero).mp hx)
    have hmem : (X ^ 2 - X : ℂ[X]).eval x ∈ spectrum ℂ (aeval N (X ^ 2 - X)) :=
      spectrum.subset_polynomial_aeval N (X ^ 2 - X) ⟨x, hspec, rfl⟩
    have hroot := mem_spectrum_iff_isRoot_charpoly.mp hmem
    have haeval : aeval N (X ^ 2 - X : ℂ[X]) = N ^ 2 - N := by simp
    rw [haeval, hchar] at hroot
    have hpow : (x ^ 2 - x) ^ Fintype.card n = 0 := by simpa [IsRoot] using hroot
    have hzero : x * (x - 1) = 0 := by linear_combination (pow_eq_zero_iff'.mp hpow).1
    rcases mul_eq_zero.mp hzero with hx0 | hx1
    · exact Or.inl hx0
    · exact Or.inr (sub_eq_zero.mp hx1)
  obtain ⟨m, hm⟩ := Multiset.exists_nat_eq_sum_of_forall_eq_zero_or_one _ hroots
  exact ⟨m, by rw [← h 1 one_pos, pow_one, trace_eq_sum_roots_charpoly, hm]⟩

end Matrix
