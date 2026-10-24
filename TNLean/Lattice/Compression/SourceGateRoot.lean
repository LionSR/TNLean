/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.NonemptyGateLabels

/-! # A participant root at each original nonempty gate occurrence

Each nonempty original gate occurrence carries a proof that its participant
set is nonempty. Selecting one of these participants therefore requires no
nonemptiness assumption on the ambient party type. An empty family of such
occurrences requires no selection.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579.
-/

namespace TNLean.Lattice.PartyCircuit.SourceCircuit
variable {P : Type}

/-- Select one participant at each original nonempty gate occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579. -/
noncomputable def sourceGateRoot {a b : Layout P} (w : SourceCircuit a b)
    (g : w.nonemptyGateLocations) : P :=
  Classical.choose g.2

/-- The selected root belongs to the original participant set.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579. -/
theorem sourceGateRoot_mem {a b : Layout P} (w : SourceCircuit a b)
    (g : w.nonemptyGateLocations) :
    sourceGateRoot w g ∈ w.participants g.1 :=
  Classical.choose_spec g.2

end TNLean.Lattice.PartyCircuit.SourceCircuit
