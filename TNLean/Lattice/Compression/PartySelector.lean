/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Logic.Basic

/-! # Selecting a single party

For any type of party labels, the selector of a party retains exactly that
party. Source: polynomial-PEPS, `04-compression.tex`, lines 233–251 and 351–381.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit
variable {P : Type}

/-- Select one original party while retaining its exact label.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
def partySelector (p : P) : P → Bool := by
  classical
  exact fun q => decide (q = p)

/-- Selecting the exterior owner is the predicate that an optional owner is absent.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
theorem partySelector_none : partySelector (none : Option P) = Option.isNone := by
  funext q
  cases q <;> simp [partySelector]

end TNLean.Lattice.PartyCircuit
