/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.LocalSourceSampleIndices
import TNLean.Lattice.Compression.SourceSampleAssignmentIndices

/-! # Restricting a reindexed common sample assignment

After the common assignment is reindexed by original gate-pair occurrences,
its values at a party's ordered slots are exactly the values supplied by
restriction to the corresponding incident sample positions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417
and 568–579.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit.SourceCircuit
open TNLean.Lattice TNLean.Lattice.PartyCircuit
variable {P : Type}

open Classical in
/-- Reindexing the common assignment commutes with restriction to the original
ordered incident slots. Only existing sample values are read.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417
and 568–579. -/
theorem restrict_reindexedSourceSampleAssignment_eq {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (k : ℕ)
    (j : Compression.DistributedOperatorContraction.Sample
      (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) → Fin k) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    (fun i : Fin (partialSlots A w).length ↦
      (allSourceSampleAssignmentEquiv w k).symm j
        ((allSourceSlotEquiv w).symm (partialSlotEquiv A w i).1)) =
      (Compression.DistributedOperatorContraction.restrictSamples
        (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1)
        k j p) ∘ partialSlotSampleEquiv w p := by
  intro A
  funext i
  rw [allSourceSampleAssignmentEquiv_symm_apply]
  rfl

end TNLean.Lattice.PartyCircuit.SourceCircuit
