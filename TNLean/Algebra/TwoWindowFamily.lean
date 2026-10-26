/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import TNLean.Algebra.TwoWindowSum

/-!
# Two windows and the complementary bond sums

Two disjoint windows of length `2 * ℓ` and the three complementary intervals
of a finite bond array form one family indexed by
`(Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3`. Its sum is the original bond sum.
All window and bulk labels are retained when their values coincide or vanish.
Empty windows and empty complementary intervals are included.

This is the additive grouping used in ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821. The tensor-factor and operator-Schmidt-rank
properties of the resulting operators are separate assertions.
-/

open scoped BigOperators

/-- The two original windows and three complementary bond sums in ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. The two inequalities
ensure that the windows are disjoint and lie in the original bond array.
All original window labels and all three bulk labels are retained. -/
def Fin.twoWindowFamily
    {A : Type*} [AddCommMonoid A] {N : ℕ} (f : Fin N → A)
    (a b ℓ : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N) :
    ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → A :=
  Sum.elim
    (Sum.elim
      (fun r ↦ f ⟨a + r.val, by omega⟩)
      (fun r ↦ f ⟨b + r.val, by omega⟩))
    ![(∑ t : Fin a, f ⟨t.val, by omega⟩),
      (∑ r : Fin (b - (a + 2 * ℓ)), f ⟨a + 2 * ℓ + r.val, by omega⟩),
      (∑ r : Fin (N - (b + 2 * ℓ)), f ⟨b + 2 * ℓ + r.val, by omega⟩)]

/-- The literal grouped family has exactly the sum of the original bond
array. This is the additive grouping in ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821; no separate Hamiltonian identity is assumed. -/
theorem Fin.sum_twoWindowFamily
    {A : Type*} [AddCommMonoid A] {N : ℕ} (f : Fin N → A)
    (a b ℓ : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N) :
    (∑ α, Fin.twoWindowFamily f a b ℓ hab hbN α) = ∑ t, f t := by
  rw [Fin.twoWindowFamily, Fintype.sum_sumElim, Fintype.sum_sumElim,
    Fin.sum_univ_three]
  rw [Fin.sum_univ_eq_five_parts_of_two_windows f a b ℓ hab hbN]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ac_rfl

/-- Additive maps preserve the literal two-window grouping. This is the
finite-sum compatibility used with the decomposition in ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. -/
theorem Fin.twoWindowFamily_map
    {A B : Type*} [AddCommMonoid A] [AddCommMonoid B] {N : ℕ}
    (f : Fin N → A) (φ : A →+ B)
    (a b ℓ : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N)
    (α : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) :
    Fin.twoWindowFamily (fun r ↦ φ (f r)) a b ℓ hab hbN α =
      φ (Fin.twoWindowFamily f a b ℓ hab hbN α) := by
  rcases α with (r | r) | t
  · rfl
  · rfl
  · fin_cases t <;> simp [Fin.twoWindowFamily]
