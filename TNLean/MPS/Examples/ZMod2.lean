/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# Z₂ group helpers for MPS examples

Shared infrastructure for MPS examples with Z₂ = `Multiplicative (ZMod 2)` symmetry.
-/

namespace MPSTensor

/-- Every element of `Multiplicative (ZMod 2)` is either `1` or `ofAdd 1`. -/
lemma zmod2_cases (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  fin_cases g <;> simp [Multiplicative.ext_iff] <;> tauto

lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

end MPSTensor
