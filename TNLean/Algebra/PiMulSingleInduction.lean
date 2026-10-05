/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Induction over coordinates of a finite product of monoids

A multiplicatively closed predicate containing the identity and every single-coordinate
function holds on every element of a finite product, without commutativity assumptions.
-/

namespace Pi

/-- Induction over single-coordinate functions in a finite product of possibly noncommutative
monoids. -/
@[elab_as_elim]
theorem mulSingle_induction_noncomm {ι : Type*} [Finite ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, Monoid (M i)] (p : (Π i, M i) → Prop) (f : Π i, M i)
    (one : p 1) (mul : ∀ f g, p f → p g → p (f * g))
    (mulSingle : ∀ i m, p (Pi.mulSingle i m)) : p f := by
  cases nonempty_fintype ι
  have h (s : Finset ι) : p (fun i ↦ if i ∈ s then f i else 1) := by
    induction s using Finset.induction_on with
    | empty => simpa [Pi.one_def] using one
    | @insert a s ha ih =>
        have heq : (fun i ↦ if i ∈ insert a s then f i else 1) =
            Pi.mulSingle a (f a) * (fun i ↦ if i ∈ s then f i else 1) := by
          funext i
          by_cases hi : i = a
          · subst i
            simp [ha]
          · simp [hi]
        rw [heq]
        exact mul _ _ (mulSingle a (f a)) ih
  simpa using h Finset.univ

end Pi
