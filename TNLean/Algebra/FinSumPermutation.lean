/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fintype.BigOperators

/-!
# Permutations of nested finite sums

This file collects the binder permutations used by finite tensor-network
contractions. Each result folds nested sums into an iterated product, reindexes
that product by an explicit equivalence, and unfolds the sums again.
-/

open scoped BigOperators

namespace Fintype

/-- Reverse three independent finite-sum binders. -/
theorem sum_reverse_three {A B C R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid R]
    (f : A → B → C → R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  let e : ((A × B) × C) ≃ ((C × B) × A) :=
    { toFun := fun x ↦ ((x.2, x.1.2), x.1.1)
      invFun := fun x ↦ ((x.2, x.1.2), x.1.1)
      left_inv := by rintro ⟨⟨a, b⟩, c⟩; rfl
      right_inv := by rintro ⟨⟨c, b⟩, a⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun x ↦ f x.1.1 x.1.2 x.2)
    (fun x ↦ f x.2 x.1.2 x.1.1)
    (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using h

/-- Move the last two of four independent finite-sum binders to the front. -/
theorem sum_last_two_first_four {A B C P R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype P] [AddCommMonoid R]
    (f : A → B → C → P → R) :
    (∑ a, ∑ b, ∑ c, ∑ p, f a b c p) = ∑ c, ∑ p, ∑ a, ∑ b, f a b c p := by
  let e : (((A × B) × C) × P) ≃ (((C × P) × A) × B) :=
    { toFun := fun x ↦ (((x.1.2, x.2), x.1.1.1), x.1.1.2)
      invFun := fun x ↦ (((x.1.2, x.2), x.1.1.1), x.1.1.2)
      left_inv := by rintro ⟨⟨⟨a, b⟩, c⟩, p⟩; rfl
      right_inv := by rintro ⟨⟨⟨c, p⟩, a⟩, b⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun x ↦ f x.1.1.1 x.1.1.2 x.1.2 x.2)
    (fun x ↦ f x.1.2 x.2 x.1.1.1 x.1.1.2)
    (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using h

/-- Permute four independent finite-sum binders from `A,B,C,P` to `P,C,A,B`. -/
theorem sum_last_first_four {A B C P R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype P] [AddCommMonoid R]
    (f : A → B → C → P → R) :
    (∑ a, ∑ b, ∑ c, ∑ p, f a b c p) = ∑ p, ∑ c, ∑ a, ∑ b, f a b c p := by
  let e : (((A × B) × C) × P) ≃ (((P × C) × A) × B) :=
    { toFun := fun x ↦ (((x.2, x.1.2), x.1.1.1), x.1.1.2)
      invFun := fun x ↦ (((x.1.2, x.2), x.1.1.2), x.1.1.1)
      left_inv := by rintro ⟨⟨⟨a, b⟩, c⟩, p⟩; rfl
      right_inv := by rintro ⟨⟨⟨p, c⟩, a⟩, b⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun x ↦ f x.1.1.1 x.1.1.2 x.1.2 x.2)
    (fun x ↦ f x.1.2 x.2 x.1.1.2 x.1.1.1)
    (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using h

/-- Move the last two of five independent finite-sum binders to the front. -/
theorem sum_last_two_first_five {A B C P Q R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype P] [Fintype Q]
    [AddCommMonoid R] (f : A → B → C → P → Q → R) :
    (∑ a, ∑ b, ∑ c, ∑ p, ∑ q, f a b c p q) =
      ∑ p, ∑ q, ∑ a, ∑ b, ∑ c, f a b c p q := by
  let e : ((((A × B) × C) × P) × Q) ≃ ((((P × Q) × A) × B) × C) :=
    { toFun := fun x ↦ ((((x.1.2, x.2), x.1.1.1.1), x.1.1.1.2), x.1.1.2)
      invFun := fun x ↦ ((((x.1.1.2, x.1.2), x.2), x.1.1.1.1), x.1.1.1.2)
      left_inv := by rintro ⟨⟨⟨⟨a, b⟩, c⟩, p⟩, q⟩; rfl
      right_inv := by rintro ⟨⟨⟨⟨p, q⟩, a⟩, b⟩, c⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun x ↦ f x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2)
    (fun x ↦ f x.1.1.2 x.1.2 x.2 x.1.1.1.1 x.1.1.1.2)
    (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using h

/-- Permute five independent finite-sum binders from `A,B,C,P,Q` to `P,B,A,C,Q`. -/
theorem sum_permute_five {A B C P Q R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype P] [Fintype Q] [AddCommMonoid R]
    (f : A → B → C → P → Q → R) :
    (∑ a, ∑ b, ∑ c, ∑ p, ∑ q, f a b c p q) =
      ∑ p, ∑ b, ∑ a, ∑ c, ∑ q, f a b c p q := by
  let e : ((((A × B) × C) × P) × Q) ≃ ((((P × B) × A) × C) × Q) :=
    { toFun := fun x ↦ ((((x.1.2, x.1.1.1.2), x.1.1.1.1), x.1.1.2), x.2)
      invFun := fun x ↦ ((((x.1.1.2, x.1.1.1.2), x.1.2), x.1.1.1.1), x.2)
      left_inv := by rintro ⟨⟨⟨⟨a, b⟩, c⟩, p⟩, q⟩; rfl
      right_inv := by rintro ⟨⟨⟨⟨p, b⟩, a⟩, c⟩, q⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun x ↦ f x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2)
    (fun x ↦ f x.1.1.2 x.1.1.1.2 x.1.2 x.1.1.1.1 x.2)
    (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using h

end Fintype
