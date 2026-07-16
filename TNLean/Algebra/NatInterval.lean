/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Order.Lemmas

/-!
# Constancy on finite natural-number intervals

This file proves that a function is constant on a finite interval when its
values agree at every pair of successive indices.

## Main results

* `eq_of_forall_succ_eq_of_mem_Icc`: equality of any two values in the interval.
-/

/-- A function on a finite interval is constant when it agrees at each pair of
successive indices. -/
theorem eq_of_forall_succ_eq_of_mem_Icc {α : Sort*} {a n i j : ℕ}
    (f : (m : ℕ) → m ≤ n → α)
    (hstep : ∀ m, a ≤ m → (hm : m < n) → f m hm.le = f (m + 1) hm)
    (hai : a ≤ i) (hin : i ≤ n) (haj : a ≤ j) (hjn : j ≤ n) :
    f i hin = f j hjn := by
  have climb : ∀ k m, a ≤ m → ∀ h : m + k ≤ n,
      f m (Nat.le_add_right m k |>.trans h) = f (m + k) h := by
    intro k
    induction k with
    | zero => intro m _ _; rfl
    | succ k ih =>
        intro m ham h
        have hmk : m + k < n := by
          apply Nat.lt_of_succ_le
          simpa [Nat.add_assoc] using h
        exact (ih m ham hmk.le).trans
          (hstep (m + k) (ham.trans (Nat.le_add_right m k)) hmk)
  rcases le_total i j with hij | hji
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact climb k i hai hjn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hji
    exact (climb k j haj hin).symm
