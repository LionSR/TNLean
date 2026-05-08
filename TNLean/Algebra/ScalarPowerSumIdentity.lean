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

This file formalizes the **finite-range power-sum identity** from arXiv:1606.00608
(Appendix A, lines 1155–1163). It provides both the same-cardinality support lemmas used in
the Appendix argument and the full unequal-cardinality statement
`sum_pow_eq_implies_multiset_eq_of_le_max_length`, which takes two lists of complex
numbers of possibly different lengths and deduces multiset equality from equality of
power sums up to the larger length.

Given two families of `n` complex scalars whose power sums agree for `1 ≤ k ≤ n`,
Newton's identities imply their diagonal matrices have equal characteristic polynomials, and
hence the families give the same multiset of values counted with multiplicity. This is the
finite-range, same-cardinality part needed before treating the full unequal-cardinality source
statement.

## Strategy

We reduce to `Matrix.charpoly_eq_of_forall_trace_pow_eq` and
`Matrix.charpoly_eq_of_trace_pow_eq_of_le_card` from `TNLean.Algebra.NewtonGirard`
by observing that the trace of a power of a diagonal matrix equals the corresponding power sum:

  `trace (diagonal a ^ k) = ∑ i, a i ^ k`

The main theorem in this file says that, for nonzero families
`a : Fin m → ℂ` and `b : Fin n → ℂ`, equality of
`∑ i : Fin m, a i ^ k` and `∑ i : Fin n, b i ^ k` for
`1 ≤ k ≤ max m n` implies `m = n` and equality of the two multisets of values.
The same-cardinality theorems are the corresponding finite-range and
all-positive-power consequences for families indexed by a single finite type.

## Relation to the source statement

The paper's Lemma `Lem:app_simple` (arXiv:1606.00608, lines 1155–1163) states:

  Let `λ_{a,k}` (k=1,…,x_a) and `λ_{b,k}` (k=1,…,x_b) be two **sorted** finite families
  of complex numbers (sorted by nonincreasing absolute value, then nondecreasing argument).
  If `∀ N ≤ max{x_a, x_b}`,
    `∑_{k=1}^{x_a} λ_{a,k}^N = ∑_{k=1}^{x_b} λ_{b,k}^N`,
  then `x_a = x_b` and `λ_{a,k} = λ_{b,k}` for all k.

The unequal-cardinality finite-range theorem below differs from the paper's list statement in
one way:

  1. **No sorting hypothesis**: we work directly with multisets through the characteristic
     polynomial, making lexicographic-phase sorting unnecessary — the polynomial equality
     absorbs the ordering.

The `Fin`-based unequal-cardinality theorem
`sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card` assumes all entries are
nonzero; the list-based theorem `sum_pow_eq_implies_multiset_eq_of_le_max_length`
drops this requirement by using the $N=0$ power sum to deduce equal lengths.
-/

open scoped Matrix BigOperators

open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n]

/-- Trace of a power of a diagonal matrix equals the power sum of the entries. -/
theorem trace_diagonal_pow [DecidableEq n] (a : n → ℂ) (k : ℕ) :
    trace (diagonal a ^ k) = ∑ i, a i ^ k := by
  classical
  simp [diagonal_pow, trace_diagonal]

/-- **Scalar power-sum identity** (same-cardinality support lemma for
`Lem:app_simple` of arXiv:1606.00608).

If two families of complex scalars, indexed by the same finite type, have equal power sums for all
positive exponents, then their characteristic polynomials (as diagonal matrices) agree. -/
theorem sum_pow_eq_implies_charpoly_diagonal_eq
    [DecidableEq n]
    (a b : n → ℂ)
    (h : ∀ k : ℕ, 0 < k → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    (diagonal a).charpoly = (diagonal b).charpoly := by
  apply charpoly_eq_of_forall_trace_pow_eq
  intro k hk
  rw [trace_diagonal_pow, trace_diagonal_pow]
  exact h k hk

/-- **Bounded scalar power-sum identity** (same-cardinality part of
`Lem:app_simple` of arXiv:1606.00608).

If two families of complex scalars, indexed by the same finite type `n`, have equal
power sums for `1 ≤ k ≤ card n`, then their characteristic polynomials as diagonal
matrices agree. -/
theorem sum_pow_eq_implies_charpoly_diagonal_eq_of_le_card
    [DecidableEq n]
    (a b : n → ℂ)
    (h : ∀ k : ℕ, 0 < k → k ≤ Fintype.card n → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    (diagonal a).charpoly = (diagonal b).charpoly := by
  apply charpoly_eq_of_trace_pow_eq_of_le_card
  intro k hk hkcard
  rw [trace_diagonal_pow, trace_diagonal_pow]
  exact h k hk hkcard

private lemma roots_prod_X_sub_C (f : n → ℂ) :
    (∏ i : n, (X - C (f i))).roots = Finset.univ.val.map f := by
  have hne : (∏ i : n, (X - C (f i))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun i _ => X_sub_C_ne_zero (f i)
  rw [roots_prod _ _ hne]
  simp

/-- Equal power sums through `card n` determine the same multiset of values for
two families indexed by the same finite type.

This is the finite-range, same-cardinality part of Lemma `Lem:app_simple` in
arXiv:1606.00608. The all-positive-power theorem below is obtained by restricting
its hypothesis to `1 ≤ k ≤ card n`. -/
theorem sum_pow_eq_implies_multiset_eq_of_le_card
    (a b : n → ℂ)
    (h : ∀ k : ℕ, 0 < k → k ≤ Fintype.card n → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    Finset.univ.val.map a = Finset.univ.val.map b := by
  classical
  have hcp := sum_pow_eq_implies_charpoly_diagonal_eq_of_le_card a b h
  rw [charpoly_diagonal, charpoly_diagonal] at hcp
  have hroots : (∏ i : n, (X - C (a i))).roots = (∏ i : n, (X - C (b i))).roots :=
    congrArg Polynomial.roots hcp
  simpa [roots_prod_X_sub_C] using hroots

/-- Equal power sums of two families indexed by the same finite type imply that the families
give rise to the same multiset of values.

This all-positive-power statement follows from
`sum_pow_eq_implies_multiset_eq_of_le_card` by restricting the hypothesis to
`1 ≤ k ≤ card n`. The theorem is still same-cardinality; Lemma `Lem:app_simple`
in arXiv:1606.00608 also proves equality of cardinalities when the sizes may
differ. -/
theorem sum_pow_eq_implies_multiset_eq
    (a b : n → ℂ)
    (h : ∀ k : ℕ, 0 < k → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    Finset.univ.val.map a = Finset.univ.val.map b :=
  sum_pow_eq_implies_multiset_eq_of_le_card a b (fun k hk _ => h k hk)

private def padFin (m N : ℕ) (a : Fin m → ℂ) : Fin N → ℂ :=
  fun i => if h : (i : ℕ) < m then a ⟨i, h⟩ else 0

private theorem sum_padFin_pow {m N : ℕ} (a : Fin m → ℂ) (hmN : m ≤ N)
    {k : ℕ} (hk : 0 < k) :
    (∑ i : Fin N, padFin m N a i ^ k) = ∑ i : Fin m, a i ^ k := by
  let fN : ℕ → ℂ := fun i => if h : i < N then padFin m N a ⟨i, h⟩ ^ k else 0
  let fm : ℕ → ℂ := fun i => if h : i < m then a ⟨i, h⟩ ^ k else 0
  have hleft :
      (∑ i : Fin N, padFin m N a i ^ k) = ∑ i ∈ Finset.range N, fN i := by
    simpa [fN] using Fin.sum_univ_eq_sum_range fN N
  have hright : (∑ i : Fin m, a i ^ k) = ∑ i ∈ Finset.range m, fm i := by
    simpa [fm] using Fin.sum_univ_eq_sum_range fm m
  rw [hleft, hright]
  rw [← Finset.sum_range_add_sum_Ico fN hmN]
  have hrange : (∑ i ∈ Finset.range m, fN i) = ∑ i ∈ Finset.range m, fm i := by
    apply Finset.sum_congr rfl
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hiN : i < N := Nat.lt_of_lt_of_le him hmN
    simp [fN, fm, padFin, him, hiN]
  have hIco : (∑ i ∈ Finset.Ico m N, fN i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hmi : m ≤ i := (Finset.mem_Ico.mp hi).1
    have hiN : i < N := (Finset.mem_Ico.mp hi).2
    simp [fN, padFin, hiN, not_lt_of_ge hmi, ne_of_gt hk]
  rw [hrange, hIco, add_zero]

private theorem count_zero_padFin {m N : ℕ} (a : Fin m → ℂ)
    (ha : ∀ i, a i ≠ 0) :
    (Finset.univ.val.map (padFin m N a)).count 0 = N - m := by
  rw [Multiset.count_map]
  rw [← Finset.filter_val]
  have hfilter :
      (Finset.univ.filter fun i : Fin N => 0 = padFin m N a i) =
        (Finset.univ.filter fun i : Fin N => m ≤ (i : ℕ)) := by
    apply Finset.ext
    intro i
    by_cases him : (i : ℕ) < m
    · have hne : ¬ 0 = a ⟨i, him⟩ := (ha ⟨i, him⟩).symm
      simp [padFin, him, hne, not_le_of_gt him]
    · simp [padFin, him, le_of_not_gt him]
  rw [hfilter]
  have hfilterIco :
      (Finset.univ.filter fun i : Fin N => m ≤ (i : ℕ)) =
        (Finset.Ico m N).attachFin (fun x hx => (Finset.mem_Ico.mp hx).2) := by
    apply Finset.ext
    intro i
    simp [Finset.mem_Ico]
  rw [hfilterIco]
  rw [← Finset.card_def, Finset.card_attachFin, Nat.card_Ico]

/-- Unequal-cardinality finite-range scalar power-sum identity under a nonzero-entry
hypothesis.

If two finite families of nonzero complex scalars have equal power sums for
`1 ≤ k ≤ max m n`, then the indexing cardinalities are equal and the two families give the
same multiset of values.  The proof pads the shorter family by zeros, applies
`sum_pow_eq_implies_multiset_eq_of_le_card`, and then counts the padded zeros. -/
theorem sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card
    (m n : ℕ) (a : Fin m → ℂ) (b : Fin n → ℂ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : ∀ k : ℕ, 0 < k → k ≤ max m n →
      ∑ i : Fin m, a i ^ k = ∑ i : Fin n, b i ^ k) :
    m = n ∧ Finset.univ.val.map a = Finset.univ.val.map b := by
  let N := max m n
  let apad : Fin N → ℂ := padFin m N a
  let bpad : Fin N → ℂ := padFin n N b
  have hpad : Finset.univ.val.map apad = Finset.univ.val.map bpad := by
    apply sum_pow_eq_implies_multiset_eq_of_le_card
    intro k hk hkcard
    rw [show (∑ i : Fin N, apad i ^ k) = ∑ i : Fin m, a i ^ k from
        sum_padFin_pow a (by dsimp [N]; exact le_max_left m n) hk,
      show (∑ i : Fin N, bpad i ^ k) = ∑ i : Fin n, b i ^ k from
        sum_padFin_pow b (by dsimp [N]; exact le_max_right m n) hk]
    exact h k hk (by simpa [N] using hkcard)
  have hcount : N - m = N - n := by
    have hcount' := congrArg (Multiset.count (0 : ℂ)) hpad
    change (Finset.univ.val.map (padFin m N a)).count 0 =
      (Finset.univ.val.map (padFin n N b)).count 0 at hcount'
    rw [count_zero_padFin a ha, count_zero_padFin b hb] at hcount'
    exact hcount'
  have hmn : m = n := by
    have hmN : m ≤ N := by dsimp [N]; exact le_max_left m n
    have hnN : n ≤ N := by dsimp [N]; exact le_max_right m n
    omega
  constructor
  · exact hmn
  subst n
  apply sum_pow_eq_implies_multiset_eq_of_le_card
  intro k hk hkcard
  exact h k hk (by simpa using hkcard)


private lemma list_pow_sum_eq_ofFn (f : Fin m → ℂ) (l : List ℂ)
    (h_ofFn : List.ofFn f = l) (k : ℕ) :
    ∑ i : Fin m, f i ^ k = (l.map fun z => z ^ k).sum := by
  calc
    ∑ i : Fin m, f i ^ k = (List.ofFn fun i : Fin m => f i ^ k).sum := by rw [List.sum_ofFn]
    _ = ((List.ofFn f).map fun z => z ^ k).sum := by
      calc
        (List.ofFn fun i : Fin m => f i ^ k).sum
            = (List.ofFn ((fun z : ℂ => z ^ k) ∘ f)).sum := rfl
        _ = ((List.ofFn f).map fun z => z ^ k).sum := by rw [← List.map_ofFn]
    _ = (l.map fun z => z ^ k).sum := by rw [h_ofFn]
/-- **Finite-range power-sum identity for possibly unequal cardinalities**
(from arXiv:1606.00608, Appendix A, lines 1155–1163).

Given two lists of complex numbers of possibly different lengths, if the power sums
agree for all $N \le \max(|la|, |lb|)$, then the two lists have the same multiset.

Uses $N=0$ (where $\lambda^0 = 1$) to deduce equal lengths, then
`sum_pow_eq_implies_multiset_eq_of_le_card` for finite-range multiset equality.
Drops the nonzero-entry hypothesis of
`sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card`. -/
theorem sum_pow_eq_implies_multiset_eq_of_le_max_length (la lb : List ℂ)
    (hp : ∀ N, N ≤ max la.length lb.length →
      (la.map fun z => z ^ N).sum = (lb.map fun z => z ^ N).sum) :
    (la : Multiset ℂ) = (lb : Multiset ℂ) := by
  -- N=0 gives cardinality equality
  have h_card : la.length = lb.length := by
    have hN0 := hp 0 (Nat.zero_le _)
    have hsum0 (l : List ℂ) : (l.map fun z => z ^ (0 : ℕ)).sum = (l.length : ℂ) := by simp
    rw [hsum0 la, hsum0 lb] at hN0
    exact_mod_cast hN0
  let m := la.length
  have hm_card : m = lb.length := h_card
  -- Convert lists to Fin m → ℂ via `List.get`; `i.val < m` is definitional
  let a : Fin m → ℂ := fun i => la.get ⟨i.val, i.is_lt⟩
  let b : Fin m → ℂ := fun i => lb.get ⟨i.val, hm_card ▸ i.is_lt⟩
  have h_ofFn_a : List.ofFn a = la := by
    apply List.ext_get
    · simp [a, m]
    · intro i hi1 hi2
      simp [a, m]
  have h_ofFn_b : List.ofFn b = lb := by
    apply List.ext_get
    · simp [b, m, hm_card]
    · intro i hi1 hi2
      simp [b, m, hm_card]
  -- Relate Fin-sum to list-sum
  have hp_fin : ∀ k, 1 ≤ k → k ≤ m → ∑ i : Fin m, a i ^ k = ∑ i : Fin m, b i ^ k := by
    intro k hk1 hk2
    have hsum_a := list_pow_sum_eq_ofFn a la h_ofFn_a k
    have hsum_b := list_pow_sum_eq_ofFn b lb h_ofFn_b k
    rw [hsum_a, hsum_b]
    apply hp k
    -- k ≤ max la.length lb.length: since k ≤ m = la.length
    exact le_max_of_le_left hk2
  -- Apply the finite-range same-cardinality lemma
  have h_mult_eq : Finset.univ.val.map a = Finset.univ.val.map b :=
    sum_pow_eq_implies_multiset_eq_of_le_card a b (fun k hk hkcard =>
      hp_fin k (by omega) (by simpa [Fintype.card_fin] using hkcard))
  -- Convert back to list multisets
  have h_multiset_a : Finset.univ.val.map a = (la : Multiset ℂ) := by
    calc
      Finset.univ.val.map a = (List.ofFn a : Multiset ℂ) := by simp
      _ = (la : Multiset ℂ) := by rw [h_ofFn_a]
  have h_multiset_b : Finset.univ.val.map b = (lb : Multiset ℂ) := by
    calc
      Finset.univ.val.map b = (List.ofFn b : Multiset ℂ) := by simp
      _ = (lb : Multiset ℂ) := by rw [h_ofFn_b]
  rw [h_multiset_a, h_multiset_b] at h_mult_eq
  exact h_mult_eq

end Matrix
