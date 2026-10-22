/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.DistributedConstructionData
import TNLean.Lattice.Compression.GateReexpansion
import TNLean.Lattice.Compression.ApproximateCircuitDensity

/-!
# An original distributed construction with prescribed gate operators

The original input and output data are accompanied by a fixed chronology and
one prescribed original operator at each nonprivate gate occurrence. The
reference monomial lists are unrestricted. Expansions may subsequently be
chosen at any fixed precision without changing the original operators,
private maps, participant sets, or chronological occurrences.

The nonempty-party convention is part of the shared original input and output
data, as recorded in `docs/paper-gaps/polypeps_nonempty_parties.tex`.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–43,
137–175 and 590–600.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit
open TNLean.Lattice.PartyCircuit

/-- Original distributed data with a fixed chronology and prescribed original
gate operators. No exact or allowed reference expansion is required.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43,
137–151 and 590–600. -/
structure GateMapConstruction (P : Type) [Fintype P]
    extends DistributedConstructionData P where
  /-- The original private operations, gate owners, and register chronology.
  Source: `04-compression.tex`, lines 21–43 and 137–151. -/
  circuit : EffectCircuit (ProductInput.wholePartyLayout initialSpace)
    (familyPhysicalLayout physicalDimension physicalOrder ++ privateOutput)
  /-- The original local operator at each nonprivate gate occurrence.
  Source: `04-compression.tex`, lines 21–43 and 590–600. -/
  gateMaps : circuit.GateMaps

namespace GateMapConstruction
variable {P : Type} [Fintype P]

/-- The original normalized product input.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139. -/
def input (C : GateMapConstruction P) :
    ProductInput (ProductInput.wholePartyLayout C.initialSpace) :=
  ProductInput.ofAllParties C.initialSpace C.initialVector C.norm_initialVector

/-- The physical density of the prescribed original operators. The retained
private registers are traced out, with no division by the output norm.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 150–153 and 590–600. -/
def physicalDensity (C : GateMapConstruction P) :
    Matrix ((p : P) → Fin (C.physicalDimension p))
      ((p : P) → Fin (C.physicalDimension p)) ℂ := by
  classical
  letI := Layout.finiteDimensional_mem_of_registers C.privateOutput C.finite_privateOutput
  let J := familyLabelledPhysicalReadout C.physicalDimension C.physicalOrder
    C.physicalOrder_nodup C.mem_physicalOrder C.privateOutput
  exact C.circuit.physicalDensityWithGateMaps C.gateMaps J C.input.vector

end GateMapConstruction
end TNLean.Lattice.PartyCircuit
