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

A function on two or three indices equals the vector of its values. These
identities rewrite a configuration on a short window into the vector notation
against which the example tensors are evaluated coordinate by coordinate.
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

end Matrix
