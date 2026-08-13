/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Cyclic expansions of matrix powers

Generic finite-matrix identities expressing entries of powers as path sums and
traces of positive powers as cyclic products.

## Main definitions

This module introduces no new definitions.

## Main results

* `Matrix.trace_pow_eq_of_intertwining`: intertwining matrices have equal trace powers when
  the intertwiner has a specified two-sided inverse.
* `pow_apply_eq_sum_path_indicator`: expands a matrix-power entry as a path sum.
* `trace_pow_eq_sum_cyclic_product`: expands a positive trace power as a cyclic sum.
-/

open scoped BigOperators Matrix

section cyclicTrace

/-! These lemmas are generic `CommSemiring`-valued matrix combinatorics. -/

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommSemiring R]

/-- If `P * B = A * P` and `Q` is a two-sided inverse of `P`, then `A` and `B` have
identical traces at every natural-number power. -/
theorem Matrix.trace_pow_eq_of_intertwining {P Q A B : Matrix n n R}
    (h : P * B = A * P) (hPQ : P * Q = 1) (hQP : Q * P = 1) (k : ℕ) :
    Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by
  calc
    Matrix.trace (A ^ k) = Matrix.trace (A ^ k * P * Q) := by
      rw [Matrix.mul_assoc, hPQ, Matrix.mul_one]
    _ = Matrix.trace (P * B ^ k * Q) := by
      rw [(show SemiconjBy P B A from h).pow_right k]
    _ = Matrix.trace (Q * P * B ^ k) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (B ^ k) := by rw [hQP, Matrix.one_mul]

/-- **Indicator-path expansion of a matrix power.** The `(a, b)` entry of `S ^ N` is the sum,
over length-`N` walks `v : Fin (N + 1) → n` from `a` to `b`, of the product of the matrix
entries along the walk.

This is the elementary combinatorial expansion of matrix powers used to derive the
cyclic-product form of `tr(S^N)` in the Lemma C.5 Case-I route.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem pow_apply_eq_sum_path_indicator (S : Matrix n n R) :
    ∀ (N : ℕ) (a b : n), (S ^ N) a b =
      ∑ v : Fin (N + 1) → n, if v 0 = a ∧ v (Fin.last N) = b
        then ∏ i : Fin N, S (v i.castSucc) (v i.succ) else 0 := by
  intro N
  induction N with
  | zero =>
    intro a b
    rw [pow_zero, Matrix.one_apply]
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) n)
      (fun v : Fin 1 → n => if v 0 = a ∧ v (Fin.last 0) = b then
        (∏ i : Fin 0, S (v i.castSucc) (v i.succ) : R) else 0)
      (fun c : n => if c = a ∧ c = b then (1 : R) else 0)
      (fun v => by simp [Equiv.funUnique_apply])]
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : ∀ c : n, ¬(c = a ∧ c = b) := fun c ⟨h1, h2⟩ => hab (h1.symm.trans h2)
      simp [hab, hne]
  | succ N ih =>
    intro a b
    have hprod : ∀ (v : Fin (N + 1) → n) (x : n),
        ∏ i : Fin (N + 1), S ((Fin.snoc v x : Fin (N + 2) → n) i.castSucc)
            ((Fin.snoc v x : Fin (N + 2) → n) i.succ) =
          (∏ i : Fin N, S (v i.castSucc) (v i.succ)) * S (v (Fin.last N)) x := by
      intro v x
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        have h1 : (Fin.snoc v x : Fin (N + 2) → n) (i.castSucc).castSucc = v i.castSucc := by
          rw [Fin.snoc_castSucc]
        have h2 : (Fin.snoc v x : Fin (N + 2) → n) (i.castSucc).succ = v i.succ := by
          rw [← Fin.castSucc_succ, Fin.snoc_castSucc]
        rw [h1, h2]
      · have h1 : (Fin.snoc v x : Fin (N + 2) → n) (Fin.last N).castSucc = v (Fin.last N) := by
          rw [Fin.snoc_castSucc]
        have h2 : (Fin.snoc v x : Fin (N + 2) → n) (Fin.last N).succ = x := by
          rw [Fin.succ_last, Fin.snoc_last]
        rw [h1, h2]
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp_rw [show ∀ (v : Fin (N + 1) → n) (c : n),
        (if v 0 = a ∧ v (Fin.last N) = c then
          (∏ i : Fin N, S (v i.castSucc) (v i.succ)) * S c b else 0) =
        (if v 0 = a then (if v (Fin.last N) = c then
          (∏ i : Fin N, S (v i.castSucc) (v i.succ)) * S c b else 0) else 0) from
      fun v c => by by_cases h : v 0 = a <;> simp [h]]
    conv_lhs => simp only [Fintype.sum_ite_eq]
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (N + 2) => n))]
    rw [Fintype.sum_prod_type]
    conv_rhs =>
      simp only [Fin.snocEquiv_apply]
      simp only [hprod]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [Finset.sum_comm]
    congr 1
    ext v
    by_cases hv0 : v 0 = a
    · simp [hv0]
    · simp [hv0]

/-- **Trace of a matrix power as a sum over cyclic products.** `tr(S^N)` is the sum, over all
labelings `k : Fin N → n` of the `N` cyclic positions, of the product of matrix entries
`S (k i) (k (i + 1))` along the cycle (indices mod `N`).

This is the cyclic-product identity used in the Lemma C.5 Case-I route to express the
doubled-index self-overlap `mpvOverlap(K.toMPSTensor, K.toMPSTensor, N)` in terms of
`tr(S^N)`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem trace_pow_eq_sum_cyclic_product (S : Matrix n n R) {N : ℕ} [NeZero N] :
    Matrix.trace (S ^ N) = ∑ k : Fin N → n, ∏ i : Fin N, S (k i) (k (i + 1)) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  have htrace : Matrix.trace (S ^ (M + 1)) = ∑ a : n, (S ^ (M + 1)) a a := by
    simp [Matrix.trace, Matrix.diag]
  rw [htrace]
  simp_rw [pow_apply_eq_sum_path_indicator S (M + 1)]
  rw [Finset.sum_comm]
  have hcollapseA : ∀ v : Fin (M + 2) → n,
      (∑ a : n, if v 0 = a ∧ v (Fin.last (M + 1)) = a then
        (∏ i : Fin (M + 1), S (v i.castSucc) (v i.succ)) else 0) =
      if v 0 = v (Fin.last (M + 1)) then
        (∏ i : Fin (M + 1), S (v i.castSucc) (v i.succ)) else 0 := by
    intro v
    by_cases h : v 0 = v (Fin.last (M + 1))
    · rw [if_pos h]
      have hswap : (fun a => if v 0 = a ∧ v (Fin.last (M + 1)) = a then
          (∏ i : Fin (M + 1), S (v i.castSucc) (v i.succ)) else (0 : R)) =
        (fun a => if v 0 = a then (if v (Fin.last (M + 1)) = a then
          (∏ i : Fin (M + 1), S (v i.castSucc) (v i.succ)) else 0) else 0) :=
        funext (fun a => by by_cases ha : v 0 = a <;> simp [ha])
      rw [hswap]
      simp [h]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg]
      rintro ⟨ha1, ha2⟩
      exact h (ha1.trans ha2.symm)
  simp_rw [hcollapseA]
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun v : Fin (M + 2) → n => Fin.init v)
    (fun k : Fin (M + 1) → n => Fin.snoc k (k 0))
  · intro v _
    exact Finset.mem_univ _
  · intro k _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (Fin.snoc k (k 0) : Fin (M + 2) → n) 0 =
      (Fin.snoc k (k 0) : Fin (M + 2) → n) (Fin.last (M + 1))
    rw [Fin.snoc_last]
    have hz : (0 : Fin (M + 2)) = (Fin.castSucc (0 : Fin (M + 1))) := (Fin.castSucc_zero).symm
    rw [hz, Fin.snoc_castSucc]
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    change (Fin.snoc (Fin.init v) ((Fin.init v) 0) : Fin (M + 2) → n) = v
    rw [show (Fin.init v) 0 = v (Fin.last (M + 1)) from by
      change v ((0 : Fin (M + 1)).castSucc) = v (Fin.last (M + 1))
      rw [Fin.castSucc_zero]
      exact hv]
    exact Fin.snoc_init_self v
  · intro k _
    funext i
    change (Fin.snoc k (k 0) : Fin (M + 2) → n) i.castSucc = k i
    simp only [Fin.snoc_castSucc]
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    apply Finset.prod_congr rfl
    intro i _
    have hi1 : v i.castSucc = (Fin.init v) i := rfl
    have hi2 : (Fin.init v) (i + 1) = v (i + 1).castSucc := rfl
    rw [hi1, hi2]
    congr 1
    cases i using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, Fin.last_add_one]
      have hz : (Fin.castSucc (0 : Fin (M + 1)) : Fin (M + 2)) = (0 : Fin (M + 2)) :=
        Fin.castSucc_zero
      rw [hz]
      exact hv.symm
    | cast j =>
      rw [Fin.coeSucc_eq_succ]
      exact congrArg v (Fin.castSucc_succ j).symm

end cyclicTrace
