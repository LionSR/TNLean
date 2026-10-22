/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.FiniteInputMemory
import TNLean.Lattice.PartyCircuit.FamilyPhysicalReadout

/-!
# Original input and output data of a distributed construction

The original party memories, normalized product input, physical output order,
and discarded private registers are shared by exact and approximate gate
constructions. Private spaces are finite-dimensional without a numerical
bound. These data include no circuit, expansion assumption, compressed
representation, or error estimate.

**Local fix (nonempty parties):** The party set is nonempty. The scalar
absorption in the source proof places an exterior scalar in an existing
party's tensor. With no parties the empty-node contraction is one, whereas
an empty-participant gate can change the output scalar. This is the existing
convention recorded in `docs/paper-gaps/polypeps_nonempty_parties.tex`.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–30,
137–151 and 565–578; `01-preliminaries.tex`, lines 5–7.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit
open TNLean.Lattice.PartyCircuit

/-- The original input and output data, on a finite nonempty party set.
There is no assumption on the size of private spaces beyond finiteness.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–30 and 137–151. -/
structure DistributedConstructionData (P : Type) [Fintype P] where
  /-- An existing party at which scalar factors can be absorbed.
  Source: `04-compression.tex`, lines 565–578; see the module convention. -/
  nonemptyParties : Nonempty P
  /-- Each party's whole original private memory.
  Source: `04-compression.tex`, lines 23–30 and 137–139. -/
  initialSpace : P → HSpace
  /-- Private dimensions are finite but need not satisfy a numerical bound.
  Source: `04-compression.tex`, lines 17–19. -/
  finite_initialSpace : ∀ p, FiniteDimensional ℂ (initialSpace p)
  /-- The original vector at each party.
  Source: `04-compression.tex`, lines 137–139. -/
  initialVector : ∀ p, initialSpace p
  /-- The original input is a product of normalized party vectors.
  Source: `04-compression.tex`, lines 137–139. -/
  norm_initialVector : ∀ p, ‖initialVector p‖ = 1
  /-- The intended physical dimension at each party.
  Source: `04-compression.tex`, lines 148–151. -/
  physicalDimension : P → ℕ
  /-- The order of the physical registers in the circuit output.
  Source: `04-compression.tex`, lines 23–30 and 148–151. -/
  physicalOrder : List P
  /-- Each party has exactly one intended physical register.
  Source: `04-compression.tex`, lines 148–151. -/
  physicalOrder_nodup : physicalOrder.Nodup
  /-- The physical output includes every original party.
  Source: `04-compression.tex`, lines 148–151. -/
  mem_physicalOrder : ∀ p, p ∈ physicalOrder
  /-- The actual private registers retained until the final trace.
  Source: `04-compression.tex`, lines 27–30 and 150–151. -/
  privateOutput : Layout P
  /-- Each discarded register is finite-dimensional, without a size bound.
  Source: `04-compression.tex`, lines 17–19 and 150–151. -/
  finite_privateOutput : ∀ r ∈ privateOutput, FiniteDimensional ℂ r.space

end TNLean.Lattice.PartyCircuit
