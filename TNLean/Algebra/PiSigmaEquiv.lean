/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Logic.Equiv.Basic

/-!
# Pointwise dependent-sum coordinates

This file records the canonical equivalence between a function taking values
in dependent sums and a dependent sum of functions.

## Main definitions

* `Equiv.piSigmaEquiv`: distributes a dependent sum pointwise over a function space.

## Tags

dependent sum, function space, equivalence
-/

namespace Equiv

/-- Distribute a dependent sum pointwise over a function space. -/
def piSigmaEquiv
    {ι : Type*} {α : ι → Type*} {β : (i : ι) → α i → Type*} :
    ((i : ι) → Σ a, β i a) ≃
      Σ a : (i : ι) → α i, (i : ι) → β i (a i) where
  toFun x := ⟨fun i ↦ (x i).1, fun i ↦ (x i).2⟩
  invFun x i := ⟨x.1 i, x.2 i⟩
  left_inv x := by
    funext i
    exact Sigma.eta (x i)
  right_inv x := by
    obtain ⟨a, b⟩ := x
    rfl

end Equiv
