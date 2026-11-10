/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Logic.Function.Basic

/-!
# Sequences with prescribed successive relations

For a family of types indexed by the natural numbers, a chosen initial value
and the existence of a successor at every value give one sequence satisfying
all successive relations simultaneously.
-/

/-- A prescribed initial value extends to a dependent sequence whenever every
value admits a successor satisfying the specified relation. -/
theorem Nat.exists_dependent_sequence {X : Nat → Type*}
    (R : ∀ i, X i → X (i + 1) → Prop) (x₀ : X 0)
    (hR : ∀ i x, ∃ y, R i x y) :
    ∃ f : (i : Nat) → X i, f 0 = x₀ ∧ ∀ i, R i (f i) (f (i + 1)) := by
  classical
  let next (i : Nat) (x : X i) : X (i + 1) := Classical.choose (hR i x)
  let f : (i : Nat) → X i := Nat.rec x₀ next
  exact ⟨f, rfl, fun i ↦ Classical.choose_spec (hR i (f i))⟩
