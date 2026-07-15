/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Equivalences for finite tuples

This file records canonical product coordinates for functions on finite index
types.  It includes right-associated coordinates in lengths three and four,
and equivalences separating the first one or two coordinates from a tuple of
arbitrary remaining length.

## Main definitions

* `finThreeArrowEquiv`: identifies a function on `Fin 3` with a right-associated triple.
* `finFourArrowEquiv`: identifies a function on `Fin 4` with a right-associated quadruple.
* `finSuccArrowEquiv`: separates the first coordinate from a finite tuple.
* `finAddTwoArrowEquiv`: separates the first two coordinates.

## Main statements

* `finSuccArrowEquiv_apply`: gives the first coordinate and the remaining tuple.
* `finSuccArrowEquiv_symm_apply`: reconstructs a tuple from its first coordinate and tail.
* `finAddTwoArrowEquiv_apply`: gives the first two coordinates and the remaining tuple.
* `finAddTwoArrowEquiv_symm_apply`: reconstructs a tuple from its first two coordinates and tail.
* `finThreeArrowEquiv_apply`: gives the ordered coordinates of the forward map.
* `finThreeArrowEquiv_symm_apply`: gives the ordered coordinates of the inverse map.
* `finFourArrowEquiv_apply`: gives the ordered coordinates of the forward map.
* `finFourArrowEquiv_symm_apply`: gives the ordered coordinates of the inverse map.

## Implementation notes

The fixed-length product coordinates are right-associated and are constructed
recursively from Mathlib's `finTwoArrowEquiv` using `Fin.consEquiv`.  The
variable-length equivalences use `Fin.consEquiv` to separate the prescribed
initial coordinates from the remaining tuple.

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

/-- The forward right-associated identification extracts the three coordinates
in order. -/
@[simp] theorem finThreeArrowEquiv_apply
    {α : Type*} (x : Fin 3 → α) :
    finThreeArrowEquiv α x = (x 0, x 1, x 2) := by
  rfl

/-- The inverse right-associated identification sends a triple to its three
coordinates in order. -/
@[simp] theorem finThreeArrowEquiv_symm_apply
    {α : Type*} (x : α × (α × α)) :
    (finThreeArrowEquiv α).symm x = ![x.1, x.2.1, x.2.2] := by
  funext i
  fin_cases i <;> rfl

/-- The forward right-associated identification extracts the four coordinates
in order. -/
@[simp] theorem finFourArrowEquiv_apply
    {α : Type*} (x : Fin 4 → α) :
    finFourArrowEquiv α x = (x 0, x 1, x 2, x 3) := by
  rfl

/-- The inverse right-associated identification sends a quadruple to its four
coordinates in order. -/
@[simp] theorem finFourArrowEquiv_symm_apply
    {α : Type*} (x : α × (α × (α × α))) :
    (finFourArrowEquiv α).symm x = ![x.1, x.2.1, x.2.2.1, x.2.2.2] := by
  funext i
  fin_cases i <;> rfl

/-! ### A fixed initial segment and a variable remaining tuple -/

/-- Separate the first coordinate from the remaining `N` coordinates. -/
def finSuccArrowEquiv (α : Type*) (N : ℕ) :
    (Fin (N + 1) → α) ≃ α × (Fin N → α) :=
  (Fin.consEquiv fun _ : Fin (N + 1) ↦ α).symm

/-- The forward identification extracts the first coordinate and the remaining tuple. -/
@[simp] theorem finSuccArrowEquiv_apply {α : Type*} (N : ℕ)
    (σ : Fin (N + 1) → α) :
    finSuccArrowEquiv α N σ = (σ 0, Fin.tail σ) :=
  rfl

/-- The inverse identification reconstructs a tuple from its first coordinate and tail. -/
@[simp] theorem finSuccArrowEquiv_symm_apply {α : Type*} (N : ℕ)
    (p : α × (Fin N → α)) :
    (finSuccArrowEquiv α N).symm p = Fin.cons p.1 p.2 :=
  rfl

/-- Separate the first two coordinates from the remaining `N` coordinates. -/
def finAddTwoArrowEquiv (α : Type*) (N : ℕ) :
    (Fin (N + 2) → α) ≃ (α × α) × (Fin N → α) :=
  (finSuccArrowEquiv α (N + 1)).trans
    ((Equiv.prodCongr (Equiv.refl α) (finSuccArrowEquiv α N)).trans
      (Equiv.prodAssoc α α (Fin N → α)).symm)

/-- The forward identification extracts the first two coordinates and the remaining tuple. -/
@[simp] theorem finAddTwoArrowEquiv_apply {α : Type*} (N : ℕ)
    (σ : Fin (N + 2) → α) :
    finAddTwoArrowEquiv α N σ = ((σ 0, σ 1), Fin.tail (Fin.tail σ)) :=
  rfl

/-- The inverse identification reconstructs a tuple from its first two coordinates and tail. -/
@[simp] theorem finAddTwoArrowEquiv_symm_apply {α : Type*} (N : ℕ)
    (p : (α × α) × (Fin N → α)) :
    (finAddTwoArrowEquiv α N).symm p = Fin.cons p.1.1 (Fin.cons p.1.2 p.2) :=
  rfl
