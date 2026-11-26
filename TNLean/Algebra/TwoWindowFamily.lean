/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import QICLean.Algebra.Combinatorics.TwoWindowSum
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

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

It also contains the following results.

* `Matrix.twoWindowFamily_eq_three_region_forms`: three-region tensor forms after grouping two
  windows.
-/

section TwoWindowFamily

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

end TwoWindowFamily

section TwoWindowTensorForms

/-!
## Three-region tensor forms after grouping two windows

The two-window family preserves the decomposition of every term other than
one selected term in each window into operators on three tensor factors.
The three regional arrays are grouped using exactly the same windows.
No finiteness or nonemptiness assumption on the tensor-factor index types
is required.

### Main results

- `Matrix.twoWindowFamily_eq_three_region_forms`: the grouped ordinary
  terms retain their three-region tensor forms.

### References

- ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821:
  the additive grouping used in the operator-Schmidt-rank argument.
-/

open scoped BigOperators Kronecker

/-- Grouping two windows preserves every ordinary three-region tensor form.
This is the additive assembly used with ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821. The original ordinary identities are the
explicit hypotheses of this auxiliary; physical locality supplies them
at the application. -/
theorem Matrix.twoWindowFamily_eq_three_region_forms
    {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    {N : ℕ}
    (H : Fin N → Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ)
    (HL : Fin N → Matrix X X ℂ) (HM : Fin N → Matrix Y Y ℂ)
    (HR : Fin N → Matrix Z Z ℂ)
    (a b ℓ : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N)
    (p s : Fin (2 * ℓ))
    (hord : ∀ r : Fin N, r.val ≠ a + p.val → r.val ≠ b + s.val →
      H r = (HL r ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ) +
        ((1 : Matrix X X ℂ) ⊗ₖ HM r) ⊗ₖ (1 : Matrix Z Z ℂ) +
        (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ HR r)
    (α : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)
    (hαL : α ≠ Sum.inl (Sum.inl p)) (hαR : α ≠ Sum.inl (Sum.inr s)) :
    Fin.twoWindowFamily H a b ℓ hab hbN α =
      (Fin.twoWindowFamily HL a b ℓ hab hbN α ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ
          (1 : Matrix Z Z ℂ) +
        ((1 : Matrix X X ℂ) ⊗ₖ Fin.twoWindowFamily HM a b ℓ hab hbN α) ⊗ₖ
          (1 : Matrix Z Z ℂ) +
        (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
          Fin.twoWindowFamily HR a b ℓ hab hbN α := by
  classical
  let k₁ : Matrix X X ℂ →ₗ[ℂ] Matrix Y Y ℂ →ₗ[ℂ]
      Matrix (X × Y) (X × Y) ℂ := Matrix.kroneckerBilinear
  let k₂ : Matrix (X × Y) (X × Y) ℂ →ₗ[ℂ] Matrix Z Z ℂ →ₗ[ℂ]
      Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ := Matrix.kroneckerBilinear
  let eL := (k₂.flip (1 : Matrix Z Z ℂ)).comp (k₁.flip (1 : Matrix Y Y ℂ))
  let eM := (k₂.flip (1 : Matrix Z Z ℂ)).comp (k₁ (1 : Matrix X X ℂ))
  let eR := k₂ (1 : Matrix (X × Y) (X × Y) ℂ)
  have hsum {k : ℕ} (idx : Fin k → Fin N)
      (hu : ∀ r, (idx r).val ≠ a + p.val)
      (hv : ∀ r, (idx r).val ≠ b + s.val) :
      (∑ r, H (idx r)) =
        ((∑ r, HL (idx r)) ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ) +
          ((1 : Matrix X X ℂ) ⊗ₖ (∑ r, HM (idx r))) ⊗ₖ (1 : Matrix Z Z ℂ) +
          (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ (∑ r, HR (idx r)) := by
    change (∑ r, H (idx r)) =
      eL (∑ r, HL (idx r)) + eM (∑ r, HM (idx r)) + eR (∑ r, HR (idx r))
    rw [map_sum, map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ ↦ hord (idx r) (hu r) (hv r)
  rcases α with (r | r) | t
  · have hrp : r ≠ p := fun h ↦ hαL (congrArg Sum.inl (congrArg Sum.inl h))
    exact hord ⟨a + r.val, by omega⟩
      (fun h ↦ hrp (Fin.ext (Nat.add_left_cancel h)))
      (show a + r.val ≠ b + s.val by omega)
  · exact hord ⟨b + r.val, by omega⟩
      (show b + r.val ≠ a + p.val by omega)
      (fun h ↦ hαR (congrArg Sum.inl (congrArg Sum.inr
        (Fin.ext (Nat.add_left_cancel h)))))
  · rcases t with ⟨t, ht⟩
    have hcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact hsum (fun r : Fin a ↦ ⟨r.val, by omega⟩)
        (fun r ↦ (show r.val ≠ a + p.val by omega))
        (fun r ↦ (show r.val ≠ b + s.val by omega))
    · exact hsum (fun r : Fin (b - (a + 2 * ℓ)) ↦
          ⟨a + 2 * ℓ + r.val, by omega⟩)
        (fun r ↦ (show a + 2 * ℓ + r.val ≠ a + p.val by omega))
        (fun r ↦ (show a + 2 * ℓ + r.val ≠ b + s.val by omega))
    · exact hsum (fun r : Fin (N - (b + 2 * ℓ)) ↦
          ⟨b + 2 * ℓ + r.val, by omega⟩)
        (fun r ↦ (show b + 2 * ℓ + r.val ≠ a + p.val by omega))
        (fun r ↦ (show b + 2 * ℓ + r.val ≠ b + s.val by omega))

end TwoWindowTensorForms
