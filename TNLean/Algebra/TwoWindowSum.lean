/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

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
