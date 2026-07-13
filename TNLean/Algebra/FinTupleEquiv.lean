/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Equivalences for short finite tuples

This file records canonical right-associated product coordinates for functions
on short finite index types.

## Main definitions

* `finThreeArrowEquiv`: identifies a function on `Fin 3` with a right-associated triple.
* `finThreeArrowEquiv_symm_apply`: gives the ordered coordinates of the inverse map.
* `finFourArrowEquiv`: identifies a function on `Fin 4` with a right-associated quadruple.

## Implementation notes

The product coordinates are right-associated and are constructed recursively
from Mathlib's `finTwoArrowEquiv` using `Fin.consEquiv`.

## Tags

finite tuples, equivalence, product coordinates
-/

/-- The canonical right-associated identification of a three-coordinate
function with a triple. -/
def finThreeArrowEquiv (α : Type*) : (Fin 3 → α) ≃ α × (α × α) :=
  (Fin.consEquiv fun _ : Fin 3 ↦ α).symm.trans
    (Equiv.prodCongr (Equiv.refl α) (finTwoArrowEquiv α))

/-- The canonical right-associated identification of a four-coordinate
function with a quadruple. -/
def finFourArrowEquiv (α : Type*) : (Fin 4 → α) ≃ α × (α × (α × α)) :=
  (Fin.consEquiv fun _ : Fin 4 ↦ α).symm.trans
    (Equiv.prodCongr (Equiv.refl α) (finThreeArrowEquiv α))

/-- The inverse right-associated identification sends a triple to its three
coordinates in order. -/
@[simp] theorem finThreeArrowEquiv_symm_apply
    {α : Type*} (x : α × (α × α)) :
    (finThreeArrowEquiv α).symm x = ![x.1, x.2.1, x.2.2] := by
  funext i
  fin_cases i <;> rfl
