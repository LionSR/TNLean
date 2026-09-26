/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Vector-notation expansion of short tuples

A function on two, three or four indices equals the vector of its values. These
identities rewrite a configuration on a short window into the vector notation
against which the example tensors are evaluated coordinate by coordinate. The
transpositions of a vector of length three are computed entrywise.
-/

namespace Matrix

/-- A function on two indices is the vector of its two values. -/
theorem eq_vecCons_fin_two {α : Type*} (f : Fin 2 → α) : f = ![f 0, f 1] := by
  ext k
  fin_cases k <;> rfl

/-- A function on three indices is the vector of its three values. -/
theorem eq_vecCons_fin_three {α : Type*} (f : Fin 3 → α) :
    f = ![f 0, f 1, f 2] := by
  ext k
  fin_cases k <;> rfl

/-- A function on four indices is the vector of its four values. -/
theorem eq_vecCons_fin_four {α : Type*} (f : Fin 4 → α) :
    f = ![f 0, f 1, f 2, f 3] := by
  ext k
  fin_cases k <;> rfl

/-- Transposing the first two entries of a vector of length three. -/
theorem vec3_comp_swap_zero_one {α : Type*} (a b c : α) :
    (![a, b, c] : Fin 3 → α) ∘ Equiv.swap 0 1 = ![b, a, c] := by
  ext x
  fin_cases x <;> rfl

/-- Transposing the last two entries of a vector of length three. -/
theorem vec3_comp_swap_one_two {α : Type*} (a b c : α) :
    (![a, b, c] : Fin 3 → α) ∘ Equiv.swap 1 2 = ![a, c, b] := by
  ext x
  fin_cases x <;> rfl

/-- Transposing the outer two entries of a vector of length three. -/
theorem vec3_comp_swap_zero_two {α : Type*} (a b c : α) :
    (![a, b, c] : Fin 3 → α) ∘ Equiv.swap 0 2 = ![c, b, a] := by
  ext x
  fin_cases x <;> rfl

end Matrix
