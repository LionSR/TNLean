/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# A finite sum separated by two windows

Two disjoint windows of length `2 * ℓ` divide a finite array into five
consecutive parts. The sum over the array is the sum over these parts,
including empty windows or empty complementary intervals. For a finite
index type `Fin N`, every shifted index is derived from the two
window-admissibility inequalities.

This is the additive identity supporting ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821. No commutation of operator products is used.
-/

open scoped BigOperators

/-- Decomposition of a finite bond sum into two windows and their three
complements. This is the additive identity underlying ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. The two windows
are required to lie in the finite bond interval. Empty complementary
intervals and windows of length zero are allowed. -/
theorem Finset.sum_range_eq_five_parts_of_two_windows
    {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    (a b ℓ N : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N) :
    (∑ t ∈ Finset.range N, f t) =
      (∑ t ∈ Finset.range a, f t) +
      (∑ r ∈ Finset.range (2 * ℓ), f (a + r)) +
      (∑ r ∈ Finset.range (b - (a + 2 * ℓ)), f (a + 2 * ℓ + r)) +
      (∑ r ∈ Finset.range (2 * ℓ), f (b + r)) +
      (∑ r ∈ Finset.range (N - (b + 2 * ℓ)), f (b + 2 * ℓ + r)) := by
  have hlast : (∑ t ∈ Finset.range N, f t) =
      (∑ t ∈ Finset.range (b + 2 * ℓ), f t) +
      ∑ r ∈ Finset.range (N - (b + 2 * ℓ)), f (b + 2 * ℓ + r) := by
    simpa only [Nat.add_sub_of_le hbN] using
      Finset.sum_range_add f (b + 2 * ℓ) (N - (b + 2 * ℓ))
  have hmiddle : (∑ t ∈ Finset.range b, f t) =
      (∑ t ∈ Finset.range (a + 2 * ℓ), f t) +
      ∑ r ∈ Finset.range (b - (a + 2 * ℓ)), f (a + 2 * ℓ + r) := by
    simpa only [Nat.add_sub_of_le hab] using
      Finset.sum_range_add f (a + 2 * ℓ) (b - (a + 2 * ℓ))
  rw [hlast, Finset.sum_range_add f b (2 * ℓ), hmiddle,
    Finset.sum_range_add f a (2 * ℓ)]


/-- The five-part window decomposition for an actual finite bond array.
Supporting additive identity for ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821. All five index bounds follow from the two
window-admissibility inequalities. -/
theorem Fin.sum_univ_eq_five_parts_of_two_windows
    {A : Type*} [AddCommMonoid A] {N : ℕ} (f : Fin N → A)
    (a b ℓ : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N) :
    (∑ t, f t) =
      (∑ t : Fin a, f ⟨t.val, by omega⟩) +
      (∑ r : Fin (2 * ℓ), f ⟨a + r.val, by omega⟩) +
      (∑ r : Fin (b - (a + 2 * ℓ)), f ⟨a + 2 * ℓ + r.val, by omega⟩) +
      (∑ r : Fin (2 * ℓ), f ⟨b + r.val, by omega⟩) +
      (∑ r : Fin (N - (b + 2 * ℓ)), f ⟨b + 2 * ℓ + r.val, by omega⟩) := by
  classical
  let g : ℕ → A := fun t ↦ if h : t < N then f ⟨t, h⟩ else 0
  have hshift (o n : ℕ) (h : o + n ≤ N) :
      (∑ r : Fin n, f ⟨o + r.val, by omega⟩) =
        ∑ r ∈ Finset.range n, g (o + r) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [g]
    rw [dite_eq_left (by omega)]
  have htotal : (∑ t, f t) = ∑ r ∈ Finset.range N, g r := by
    simpa only [Nat.zero_add] using hshift 0 N (by omega)
  have hhead : (∑ t : Fin a, f ⟨t.val, by omega⟩) =
      ∑ r ∈ Finset.range a, g r := by
    simpa only [Nat.zero_add] using hshift 0 a (by omega)
  rw [htotal, hhead, hshift a (2 * ℓ) (by omega),
    hshift (a + 2 * ℓ) (b - (a + 2 * ℓ)) (by omega),
    hshift b (2 * ℓ) hbN, hshift (b + 2 * ℓ) (N - (b + 2 * ℓ)) (by omega)]
  exact Finset.sum_range_eq_five_parts_of_two_windows g a b ℓ N hab hbN


section

open Matrix

open scoped BigOperators Kronecker

section

open scoped BigOperators

section

open scoped BigOperators

namespace Finset

/-- A finite shifted window enumerates exactly the corresponding interval
of bond starts. Auxiliary indexing identity for ALVV, `eq:H-mid-cut`,
lines 810–821. Empty windows and empty ambient intervals are allowed. -/
private theorem sum_fin_window_eq_filter
    {M : Type*} [AddCommMonoid M] {N : ℕ} (h : Fin N → M)
    (o n : ℕ) (hon : o + n ≤ N) :
    (∑ r : Fin n, h ⟨o + r.val, by omega⟩) =
      ∑ i ∈ (univ : Finset (Fin N)).filter
        (fun i ↦ o ≤ i.val ∧ i.val < o + n), h i := by
  classical
  refine Finset.sum_bij
    (fun r _ ↦ (⟨o + r.val, by omega⟩ : Fin N)) ?_ ?_ ?_ ?_
  · intro r _
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> omega
  · intro r _ s _ hrs
    apply Fin.ext
    have heq := congrArg Fin.val hrs
    exact Nat.add_left_cancel heq
  · intro i hi
    have hip := (mem_filter.mp hi).2
    refine ⟨⟨i.val - o, by omega⟩, mem_univ _, ?_⟩
    apply Fin.ext
    change o + (i.val - o) = i.val
    omega
  · intro r _
    rfl
end Finset

namespace Fin

/-- The actual even-numbered regional internal sums and the two complete
bond windows reproduce the original Hamiltonian sum. Auxiliary to ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
`def:hard-trunc`, lines 873–886. Every original bond is retained once.
The identity includes zero-length windows. -/
theorem sum_univ_eq_actual_two_window_alphabet
    {M : Type*} [AddCommMonoid M] (L a b ell : ℕ)
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (h : Fin (L - 1) → M) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → M := fun j ↦ ∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let WL : Fin (2 * ell) → M := fun r ↦ h ⟨a + r.val, by omega⟩
    let WR : Fin (2 * ell) → M := fun r ↦ h ⟨b + r.val, by omega⟩
    (∑ i, h i) = A 0 + (∑ r, WL r) + A 2 + (∑ r, WR r) + A 4 := by
  classical
  intro k A WL WR
  change (∑ i, h i) =
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ 0 ≤ i.val ∧ i.val + 1 < a + 1), h i) +
    (∑ r : Fin (2 * ell), h ⟨a + r.val, by omega⟩) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ a + 2 * ell ≤ i.val ∧ i.val + 1 < b + 1), h i) +
    (∑ r : Fin (2 * ell), h ⟨b + r.val, by omega⟩) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ b + 2 * ell ≤ i.val ∧ i.val + 1 < L), h i)
  rw [Finset.sum_fin_window_eq_filter h a (2 * ell) (by omega),
    Finset.sum_fin_window_eq_filter h b (2 * ell) hb]
  simp only [Finset.sum_filter]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  have hcover :
      (0 ≤ i.val ∧ i.val + 1 < a + 1) ∨
      (a ≤ i.val ∧ i.val < a + 2 * ell) ∨
      (a + 2 * ell ≤ i.val ∧ i.val + 1 < b + 1) ∨
      (b ≤ i.val ∧ i.val < b + 2 * ell) ∨
      (b + 2 * ell ≤ i.val ∧ i.val + 1 < L) := by omega
  rcases hcover with h0 | hL | hM | hR | h4
  all_goals simp (disch := omega) only [ite_eq_left, ite_eq_right]
  all_goals simp
end Fin
end
end
end
