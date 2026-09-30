/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite tuples as lists

This file records generic compatibility results between `Fin` tuple constructors
and `List.ofFn`, and the destructuring step `List.exists_eq_ofFn` that brings an
arbitrary list to the form `List.ofFn σ` on which word evaluations are computed.
-/

namespace List

/-- Appending one value to a finite tuple appends the same value to its list. -/
theorem ofFn_snoc {α : Type*} {n : ℕ} (f : Fin n → α) (x : α) :
    List.ofFn (Fin.snoc f x) = List.ofFn f ++ [x] := by
  conv_lhs => rw [List.ofFn_succ' (Fin.snoc f x)]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Every list is `List.ofFn` of some function on `Fin n`, namely its own `get`; a proof can
write `obtain ⟨L, σ, rfl⟩ := List.exists_eq_ofFn w`. -/
theorem exists_eq_ofFn {α : Type*} (l : List α) : ∃ n, ∃ f : Fin n → α, l = List.ofFn f :=
  ⟨_, _, (List.ofFn_get l).symm⟩

end List
