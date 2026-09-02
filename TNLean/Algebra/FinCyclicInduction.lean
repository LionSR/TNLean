/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Finite cyclic-index identities

This file records an induction principle for a nonempty finite cyclic index and
the action of one-step rotation on nonterminal indices.
-/

namespace Fin

/-- A predicate that holds at `0` and is closed under `· + 1` holds at every
index, because `+1` generates the cyclic group from `0`. Proved by induction on
`i.val`: the predecessor of a nonzero `i` is `⟨i.val - 1, _⟩`, whose successor
is `i`. -/
theorem cyclic_induction {m : ℕ} [NeZero m] {P : Fin m → Prop}
    (h0 : P 0) (hstep : ∀ i : Fin m, P i → P (i + 1)) (i : Fin m) : P i := by
  induction hi : i.val generalizing i with
  | zero => obtain rfl : i = 0 := Fin.ext (by simpa using hi); exact h0
  | succ k ih =>
    have hk : k < m := by have := i.isLt; omega
    have e : (⟨k, hk⟩ : Fin m) + 1 = i := by
      apply Fin.ext
      have hmod_one : 1 < m := by omega
      have hone : (1 : Fin m).val = 1 := by
        have : (1 : Fin m).val = 1 % m := Fin.val_one' m
        rw [this]; exact Nat.mod_eq_of_lt hmod_one
      rw [Fin.val_add, Fin.val_mk, hone, hi]
      exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
    rw [← e]
    exact hstep _ (ih ⟨k, hk⟩ rfl)

/-- One-step rotation on `Fin (N + 1)` sends the nonterminal embedding of
`i : Fin N` to its ordinary successor. -/
lemma finRotate_succ_castSucc {N : ℕ} (i : Fin N) :
    finRotate (N + 1) i.castSucc = i.succ := by
  have h := finRotate_of_lt (n := N) i.isLt
  have e1 : (⟨(i : ℕ), i.isLt.trans_le N.le_succ⟩ : Fin (N + 1)) = i.castSucc := Fin.ext rfl
  have e2 : (⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (N + 1)) = i.succ := Fin.ext rfl
  rw [e1, e2] at h
  exact h

end Fin
