/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Network.DistributedContraction.LocalSourceSampleIndices
import TNLean.Network.DistributedContraction.SourceSampleAssignmentIndices

/-! # Restricting a reindexed common sample assignment

After the common assignment is reindexed by original gate-pair occurrences,
its values at a party's ordered slots are exactly the values supplied by
restriction to the corresponding incident sample positions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417
and 568–579.
-/

noncomputable section
namespace QuantumCircuit.Party.SourceCircuit
open TNLean.Network
variable {P : Type} [DecidableEq P]

open Classical in
/-- Reindexing the common assignment commutes with restriction to the original
ordered incident slots. Only existing sample values are read.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417
and 568–579. -/
theorem restrict_reindexedSourceSampleAssignment_eq {X Y : P → Type}
    (w : SourceCircuit X Y) (p : P) (k : ℕ)
    (j : DistributedOperatorContraction.Sample
      (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) → Fin k) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    (fun i : Fin (partialSlots A w).length ↦
      (allSourceSampleAssignmentEquiv w k).symm j
        ((allSourceSlotEquiv w).symm (partialSlotEquiv A w i).1)) =
      (DistributedOperatorContraction.restrictSamples
        (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1)
        k j p) ∘ partialSlotSampleEquiv w p := by
  intro A
  funext i
  rw [allSourceSampleAssignmentEquiv_symm_apply]
  rfl

end QuantumCircuit.Party.SourceCircuit
