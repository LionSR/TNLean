/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinCyclicInduction
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Coordinates on one cyclic translation orbit

The additive order of a translation step is exactly the number of distinct
points in each orbit. A finite cyclic coordinate enumerates an orbit once,
and one-step rotation of that coordinate translates the point by the step.
These elementary identities are used in the blocked cyclic-sector argument
of arXiv:1708.00029, Section 4.1.
-/

/-- An additive orbit is enumerated without repetition up to the order of
its step. Source: arXiv:1708.00029, Section 4.1. -/
theorem ZMod.orbitIndex_injective {m n : ℕ} [NeZero m]
    (p u : ZMod m) (hord : addOrderOf p = n + 1) :
    Function.Injective (fun t : Fin (n + 1) => u + t.val • p) := by
  intro i j hij
  apply Fin.ext
  apply (nsmul_injOn_Iio_addOrderOf (x := p))
  · rw [hord]
    exact i.isLt
  · rw [hord]
    exact j.isLt
  exact add_left_cancel hij

/-- Rotating a finite orbit coordinate advances the corresponding point
by one translation step. Source: arXiv:1708.00029, Section 4.1. -/
theorem ZMod.orbitIndex_finRotate {m n : ℕ} [NeZero m]
    (p u : ZMod m) (hord : addOrderOf p = n + 1)
    (t : Fin (n + 1)) :
    u + (finRotate (n + 1) t).val • p =
      (u + t.val • p) + p := by
  have hzero : (n + 1) • p = 0 := by
    simpa only [hord] using addOrderOf_nsmul_eq_zero p
  by_cases ht : t = Fin.last n
  · subst t
    rw [finRotate_last, Fin.val_zero, Fin.val_last]
    simp only [zero_nsmul, add_zero]
    rw [add_assoc, ← succ_nsmul, hzero, add_zero]
  · rw [coe_finRotate_of_ne_last ht, succ_nsmul]
    ac_rfl
