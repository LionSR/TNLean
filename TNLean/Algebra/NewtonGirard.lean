/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

/-!
# Newton-Girard Trace Recursion for Characteristic Polynomial

This file proves the Newton-Girard recursion relating the coefficients of the
reverse characteristic polynomial `charpolyRev(M) = det(1 - X·M)` to traces of
matrix powers, and derives that equal traces of all powers implies equal
characteristic polynomials.

## Main results

* `Matrix.newton_girard_charpolyRev_coeff`: The Newton-Girard recursion
  `(m+1) · p_{m+1} = -∑_{j=0}^{m} p_j · tr(M^{m+1-j})`
  where `p_k = charpolyRev(M).coeff k`.

* `Matrix.charpolyRev_eq_of_forall_trace_pow_eq`: If `tr(A^k) = tr(B^k)` for
  all `k ≥ 1`, then `A.charpolyRev = B.charpolyRev`.

* `Matrix.charpolyRev_eq_of_trace_pow_eq_of_le_card`: If `tr(A^k) = tr(B^k)`
  for `1 ≤ k ≤ card n`, then `A.charpolyRev = B.charpolyRev`.

* `Matrix.charpoly_eq_of_forall_trace_pow_eq`: If `tr(A^k) = tr(B^k)` for all
  `k ≥ 1`, then `A.charpoly = B.charpoly`.

## Proof strategy

The Newton-Girard recursion follows from differentiating `P(X) = det(1 - X·M)`
and using the adjugate identity `adj(1 - X·M) · (1 - X·M) = P(X) · I`.
Specifically, Jacobi's formula gives `P'(X) = -tr(adj(1 - X·M) * M.map C)`,
and expanding the adjugate in powers of X and comparing coefficients yields the
recursion.

The downstream results (charpolyRev equality and charpoly equality) follow from
the recursion by strong induction on the coefficient index, using the fact that
`(m+1 : R) ≠ 0` in characteristic zero rings for cancellation.
-/


open scoped Matrix BigOperators
open Polynomial Finset Matrix

namespace Matrix

variable {R : Type*} [CommRing R]
variable {n : Type*} [DecidableEq n] [Fintype n]

/-! ### Auxiliary lemmas for the Newton-Girard proof -/

private lemma derivative_det_eq_sum (A : Matrix n n R[X]) :
    derivative A.det =
    ∑ j : n, (A.updateCol j (fun k => derivative (A k j))).det := by
  rw [det_apply]
  simp only [map_sum]
  trans ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ •
      ∑ j ∈ Finset.univ, (∏ k ∈ Finset.univ.erase j, A (σ k) k) * derivative (A (σ j) j)
  · apply Finset.sum_congr rfl
    intro σ _
    calc
      derivative (Equiv.Perm.sign σ • ∏ i : n, A (σ i) i)
          = Equiv.Perm.sign σ • derivative (∏ i : n, A (σ i) i) := by
            simp
      _ = Equiv.Perm.sign σ •
            ∑ j ∈ Finset.univ, (∏ k ∈ Finset.univ.erase j, A (σ k) k) *
              derivative (A (σ j) j) := by
            exact congrArg (fun p ↦ Equiv.Perm.sign σ • p) derivative_prod_finset
  · trans ∑ j : n, ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ •
        ((∏ k ∈ Finset.univ.erase j, A (σ k) k) * derivative (A (σ j) j))
    · trans ∑ σ : Equiv.Perm n, ∑ j : n, Equiv.Perm.sign σ •
          ((∏ k ∈ Finset.univ.erase j, A (σ k) k) * derivative (A (σ j) j))
      · apply Finset.sum_congr rfl
        intro σ _
        simpa using
          (Finset.smul_sum
            (r := Equiv.Perm.sign σ)
            (s := Finset.univ)
            (f := fun j : n =>
              (∏ k ∈ Finset.univ.erase j, A (σ k) k) * derivative (A (σ j) j)))
      · simpa using
          (Finset.sum_comm :
            (∑ σ : Equiv.Perm n, ∑ j : n,
              Equiv.Perm.sign σ •
                ((∏ k ∈ Finset.univ.erase j, A (σ k) k) * derivative (A (σ j) j))) =
            ∑ j : n, ∑ σ : Equiv.Perm n,
              Equiv.Perm.sign σ •
                ((∏ k ∈ Finset.univ.erase j, A (σ k) k) * derivative (A (σ j) j)))
    · apply Finset.sum_congr rfl
      intro j _
      rw [det_apply]
      apply Finset.sum_congr rfl
      intro σ _
      congr 2
      symm
      calc ∏ i : n, (A.updateCol j (fun k => derivative (A k j))) (σ i) i
          = ∏ i ∈ Finset.univ, (A.updateCol j (fun k => derivative (A k j))) (σ i) i := rfl
        _ = (∏ i ∈ Finset.univ.erase j,
              (A.updateCol j (fun k => derivative (A k j))) (σ i) i) *
            (A.updateCol j (fun k => derivative (A k j))) (σ j) j :=
              (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
        _ = (∏ i ∈ Finset.univ.erase j, A (σ i) i) * derivative (A (σ j) j) := by
            rw [updateCol_self]
            congr 1
            apply Finset.prod_congr rfl
            intro i hi
            rw [Finset.mem_erase] at hi
            rw [updateCol_ne hi.1]

private lemma det_updateCol_eq_adjugate_mulVec (A : Matrix n n R[X]) (j : n) (b : n → R[X]) :
    (A.updateCol j b).det = ∑ k : n, A.adjugate j k * b k := by
  rw [← cramer_apply, cramer_eq_adjugate_mulVec]; simp [mulVec, dotProduct]

omit [Fintype n] in
private lemma derivative_entry_F (M : Matrix n n R) (i j : n) :
    derivative ((1 - (X : R[X]) • M.map C) i j) = -C (M i j) := by
  by_cases h : i = j
  · subst h
    simp [derivative_mul]
  · simp [h, derivative_mul]

private lemma jacobi_formula_charpolyRev (M : Matrix n n R) :
    derivative (M.charpolyRev) =
    -Matrix.trace (M.map C * (1 - (X : R[X]) • M.map C).adjugate) := by
  unfold charpolyRev
  rw [derivative_det_eq_sum]
  simp only [derivative_entry_F]
  simp_rw [det_updateCol_eq_adjugate_mulVec]
  simp only [mul_neg, Finset.sum_neg_distrib]
  congr 1
  simp only [trace, diag_apply, mul_apply, map_apply]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma map_C_pow (M : Matrix n n R) (l : ℕ) :
    (M.map C) ^ l = (M ^ l).map (C : R → R[X]) := by
  induction l with
  | zero => simp [Matrix.map_one]
  | succ l ih => simp [pow_succ, ih, Matrix.map_mul]

omit [DecidableEq n] in
private lemma trace_map_C (M : Matrix n n R) :
    Matrix.trace (M.map (C : R → R[X])) = C (Matrix.trace M) := by
  simp [Matrix.trace, map_apply, map_sum]

private noncomputable def T_trace (M : Matrix n n R) (l : ℕ) : R[X] :=
  Matrix.trace ((M.map C) ^ l * (1 - (X : R[X]) • M.map C).adjugate)

private lemma T_trace_recursion (M : Matrix n n R) (l : ℕ) :
    T_trace M l - X * T_trace M (l + 1) =
    M.charpolyRev * C (Matrix.trace (M ^ l)) := by
  unfold T_trace charpolyRev
  set F := (1 : Matrix n n R[X]) - (X : R[X]) • M.map C
  set Adj := F.adjugate
  have hadj : Adj * F = F.det • 1 := adjugate_mul F
  have h_mul : (M.map C) ^ l * Adj * F = F.det • (M.map C) ^ l := by
    calc
      (M.map C) ^ l * Adj * F = (M.map C) ^ l * (Adj * F) := by
        simp [Matrix.mul_assoc]
      _ = (M.map C) ^ l * (F.det • (1 : Matrix n n R[X])) := by
        simp [hadj]
      _ = F.det • ((M.map C) ^ l * (1 : Matrix n n R[X])) := by
        simp
      _ = F.det • (M.map C) ^ l := by
        simp
  have h_rhs : Matrix.trace (F.det • (M.map C) ^ l) =
      F.det * C (Matrix.trace (M ^ l)) := by
    rw [Matrix.trace_smul, smul_eq_mul, map_C_pow, trace_map_C]
  have hf : (M.map C) ^ l * Adj * F =
      (M.map C) ^ l * Adj - (X : R[X]) • ((M.map C) ^ l * Adj * M.map C) := by
    have hFF : F = (1 : Matrix n n R[X]) - (X : R[X]) • M.map C := rfl
    rw [hFF, Matrix.mul_sub, Matrix.mul_one]
    congr 1
    rw [mul_smul_comm]
  have h_lhs : Matrix.trace ((M.map C) ^ l * Adj * F) =
      Matrix.trace ((M.map C) ^ l * Adj) -
      X * Matrix.trace ((M.map C) ^ (l + 1) * Adj) := by
    rw [hf, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
    congr 1
    rw [trace_mul_comm ((M.map C) ^ l * Adj) (M.map C)]
    congr 1
    rw [← Matrix.mul_assoc, ← pow_succ']
  have h4 := congr_arg Matrix.trace h_mul
  rw [h_lhs, h_rhs] at h4
  exact h4

private lemma T_trace_coeff (M : Matrix n n R) (l m : ℕ) :
    (T_trace M (l + 1)).coeff m =
    ∑ j ∈ range (m + 1), M.charpolyRev.coeff j * Matrix.trace (M ^ (l + m + 1 - j)) := by
  induction m generalizing l with
  | zero =>
    have hrec := T_trace_recursion M (l + 1)
    have h0 := congr_arg (fun p => p.coeff 0) hrec
    simp only [coeff_sub, coeff_X_mul_zero, sub_zero, coeff_mul_C] at h0
    rw [Finset.sum_range_one]
    convert h0 using 2
  | succ m ih =>
    have hrec := T_trace_recursion M (l + 1)
    have hcoeff_eq : (T_trace M (l + 1)).coeff (m + 1) - (T_trace M (l + 2)).coeff m =
        M.charpolyRev.coeff (m + 1) * Matrix.trace (M ^ (l + 1)) := by
      have := congr_arg (fun p => p.coeff (m + 1)) hrec
      simp only [coeff_sub, Polynomial.coeff_X_mul, coeff_mul_C] at this
      linear_combination this
    have ih_l1 := ih (l + 1)
    have hcoeff : (T_trace M (l + 1)).coeff (m + 1) =
        M.charpolyRev.coeff (m + 1) * Matrix.trace (M ^ (l + 1)) +
        ∑ j ∈ range (m + 1), M.charpolyRev.coeff j * Matrix.trace (M ^ (l + 1 + m + 1 - j)) := by
      linear_combination hcoeff_eq + ih_l1
    rw [hcoeff]
    symm
    rw [Finset.sum_range_succ, add_comm]
    congr 1
    · have : l + (m + 1) + 1 - (m + 1) = l + 1 := by omega
      rw [this]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have : l + (m + 1) + 1 - j = l + 1 + m + 1 - j := by omega
      rw [this]

/-! ### Newton-Girard Recursion -/

/-- **Newton-Girard trace recursion** for `charpolyRev` coefficients.

For an `n × n` matrix `M`, writing `P(X) = charpolyRev(M) = det(1 - X·M)` and
`p_k = P.coeff k`, we have:

  `(m+1) · p_{m+1} = -∑_{j=0}^{m} p_j · tr(M^{m+1-j})`

This is derived from Jacobi's formula `P'(X) = -tr(adj(1 - X·M) · M.map C)`
and the trace function `T(l) = tr((M.map C)^l · adj(1 - X·M))`, whose
coefficients are extracted by induction from the adjugate identity
`adj(F) · F = det(F) · I`.
-/
theorem newton_girard_charpolyRev_coeff (M : Matrix n n R) (m : ℕ) :
    (↑(m + 1) : R) * (M.charpolyRev).coeff (m + 1) =
    -(∑ j ∈ range (m + 1), (M.charpolyRev).coeff j * trace (M ^ (m + 1 - j))) := by
  have hjac := jacobi_formula_charpolyRev M
  have hder : (derivative M.charpolyRev).coeff m =
      M.charpolyRev.coeff (m + 1) * (↑m + 1) := coeff_derivative M.charpolyRev m
  have hjac_coeff : (derivative M.charpolyRev).coeff m = -(T_trace M 1).coeff m := by
    rw [hjac, coeff_neg]; unfold T_trace; simp [pow_one]
  have ht := T_trace_coeff M 0 m
  simp only [zero_add] at ht
  rw [hjac_coeff, ht] at hder
  have hcast : (↑(m + 1) : R) = (↑m : R) + 1 := by push_cast; ring
  rw [hcast, mul_comm]
  exact hder.symm

/-! ### Equality of characteristic polynomials from traces -/

section CharZeroDomain

variable [CharZero R] [IsDomain R]

/-- `charpolyRev` coefficients are uniquely determined by traces of powers.

If `tr(A^k) = tr(B^k)` for all `k ≥ 1`, then `A.charpolyRev = B.charpolyRev`.

**Proof**: By strong induction on the coefficient index.
- Base case (`m = 0`): Both `charpolyRev` polynomials evaluate to `1` at `0`,
  so the constant coefficients agree.
- Inductive step (`m + 1`): The Newton-Girard recursion gives
  `(m+1) · p_{m+1}(A) = -∑ p_j(A) · tr(A^{m+1-j})`
  and similarly for `B`. By induction hypothesis, `p_j(A) = p_j(B)` for `j ≤ m`,
  and by hypothesis, `tr(A^k) = tr(B^k)` for `k ≥ 1`. Thus the right-hand
  sides are equal, so `(m+1) · p_{m+1}(A) = (m+1) · p_{m+1}(B)`. Since
  `(m+1 : R) ≠ 0` in characteristic zero and `R` is a domain (so has no zero
  divisors), we can cancel to get `p_{m+1}(A) = p_{m+1}(B)`.
-/
theorem charpolyRev_eq_of_forall_trace_pow_eq
    (A B : Matrix n n R)
    (h : ∀ k : ℕ, 0 < k → trace (A ^ k) = trace (B ^ k)) :
    A.charpolyRev = B.charpolyRev := by
  suffices ∀ m : ℕ, A.charpolyRev.coeff m = B.charpolyRev.coeff m from
    Polynomial.ext this
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 =>
      rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, eval_charpolyRev, eval_charpolyRev]
    | m + 1 =>
      have hA := newton_girard_charpolyRev_coeff A m
      have hB := newton_girard_charpolyRev_coeff B m
      -- The sums on the right-hand side are equal by IH and trace hypothesis
      have h_sum_eq : ∑ j ∈ range (m + 1), (A.charpolyRev).coeff j * trace (A ^ (m + 1 - j)) =
          ∑ j ∈ range (m + 1), (B.charpolyRev).coeff j * trace (B ^ (m + 1 - j)) := by
        apply sum_congr rfl
        intro j hj
        rw [mem_range] at hj
        rw [ih j (by omega), h (m + 1 - j) (by omega)]
      -- So (m+1) * p_{m+1}(A) = (m+1) * p_{m+1}(B)
      have heq : (↑(m + 1) : R) * A.charpolyRev.coeff (m + 1) =
                 (↑(m + 1) : R) * B.charpolyRev.coeff (m + 1) := by
        rw [hA, hB, h_sum_eq]
      -- Cancel (m+1) since it's nonzero in CharZero
      have hm_ne : (↑(m + 1) : R) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      exact mul_left_cancel₀ hm_ne heq

/-- `charpolyRev` coefficients are determined by the first `card n` traces of powers.

For an `n × n` matrix, the Newton--Girard recursion for coefficient `m+1` only uses
the traces `tr(M^k)` with `1 ≤ k ≤ m+1`. Coefficients above `card n` vanish for
`charpolyRev`, so traces through degree `card n` determine the whole polynomial. -/
theorem charpolyRev_eq_of_trace_pow_eq_of_le_card
    (A B : Matrix n n R)
    (h : ∀ k : ℕ, 0 < k → k ≤ Fintype.card n → trace (A ^ k) = trace (B ^ k)) :
    A.charpolyRev = B.charpolyRev := by
  suffices ∀ m : ℕ, A.charpolyRev.coeff m = B.charpolyRev.coeff m from
    Polynomial.ext this
  intro m
  by_cases hm_card : m ≤ Fintype.card n
  · induction m using Nat.strong_induction_on with
    | _ m ih =>
      match m with
      | 0 =>
        rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, eval_charpolyRev, eval_charpolyRev]
      | m + 1 =>
        have hA := newton_girard_charpolyRev_coeff A m
        have hB := newton_girard_charpolyRev_coeff B m
        have h_sum_eq :
            ∑ j ∈ range (m + 1), (A.charpolyRev).coeff j * trace (A ^ (m + 1 - j)) =
              ∑ j ∈ range (m + 1), (B.charpolyRev).coeff j *
                trace (B ^ (m + 1 - j)) := by
          apply sum_congr rfl
          intro j hj
          rw [mem_range] at hj
          rw [ih j (by omega) (by omega),
            h (m + 1 - j) (by omega) (by omega)]
        have heq : (↑(m + 1) : R) * A.charpolyRev.coeff (m + 1) =
                   (↑(m + 1) : R) * B.charpolyRev.coeff (m + 1) := by
          rw [hA, hB, h_sum_eq]
        have hm_ne : (↑(m + 1) : R) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        exact mul_left_cancel₀ hm_ne heq
  · have hA : A.charpolyRev.coeff m = 0 := by
      have hdeg : A.charpolyRev.natDegree ≤ Fintype.card n := by
        rw [← reverse_charpoly A]
        exact (reverse_natDegree_le A.charpoly).trans_eq (charpoly_natDegree_eq_dim A)
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))
    have hB : B.charpolyRev.coeff m = 0 := by
      have hdeg : B.charpolyRev.natDegree ≤ Fintype.card n := by
        rw [← reverse_charpoly B]
        exact (reverse_natDegree_le B.charpoly).trans_eq (charpoly_natDegree_eq_dim B)
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))
    rw [hA, hB]

omit [IsDomain R] in
private lemma charpoly_eq_of_charpolyRev_eq
    (A B : Matrix n n R)
    (hrev : A.charpolyRev = B.charpolyRev) :
    A.charpoly = B.charpoly := by
  have hrA := reverse_charpoly A
  have hrB := reverse_charpoly B
  have h_rev_eq : A.charpoly.reverse = B.charpoly.reverse := by
    rw [hrA, hrB, hrev]
  have hdA := charpoly_natDegree_eq_dim A
  have hdB := charpoly_natDegree_eq_dim B
  rw [Polynomial.reverse, Polynomial.reverse, hdA, hdB] at h_rev_eq
  have := congr_arg (Polynomial.reflect (Fintype.card n)) h_rev_eq
  rwa [Polynomial.reflect_reflect, Polynomial.reflect_reflect] at this

/-- **Main result**: If `tr(A^k) = tr(B^k)` for all `k ≥ 1`, then
`A.charpoly = B.charpoly`.

Follows from `charpolyRev_eq_of_forall_trace_pow_eq` using the fact that
`charpoly` and `charpolyRev` determine each other via polynomial reversal.
-/
theorem charpoly_eq_of_forall_trace_pow_eq
    (A B : Matrix n n R)
    (h : ∀ k : ℕ, 0 < k → trace (A ^ k) = trace (B ^ k)) :
    A.charpoly = B.charpoly := by
  have hrev : A.charpolyRev = B.charpolyRev :=
    charpolyRev_eq_of_forall_trace_pow_eq A B h
  exact charpoly_eq_of_charpolyRev_eq A B hrev

/-- If `tr(A^k) = tr(B^k)` for `1 ≤ k ≤ card n`, then `A.charpoly = B.charpoly`. -/
theorem charpoly_eq_of_trace_pow_eq_of_le_card
    (A B : Matrix n n R)
    (h : ∀ k : ℕ, 0 < k → k ≤ Fintype.card n → trace (A ^ k) = trace (B ^ k)) :
    A.charpoly = B.charpoly := by
  have hrev : A.charpolyRev = B.charpolyRev :=
    charpolyRev_eq_of_trace_pow_eq_of_le_card A B h
  exact charpoly_eq_of_charpolyRev_eq A B hrev

end CharZeroDomain

end Matrix
