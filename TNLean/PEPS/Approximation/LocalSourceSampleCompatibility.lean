/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.LocalSourceSampleIndices

/-! # Restricting an original sample assignment to incident source positions

The local sample equivalence preserves the original source occurrence.
A supplied global assignment therefore restricts to the ordered incident slots
without choosing a value at any other source position.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417
and 568–579.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit.SourceCircuit
open TNLean.PEPS TNLean.PEPS.PairEffect
open TNLean.PEPS.Approximation
variable {P : Type}

open Classical in
/-- Restriction through the distributed incident-sample indices is exactly
restriction through the original ordered source-slot indices. No extension
of a local assignment is used. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–417 and 568–579. -/
theorem restrict_sourceSampleAssignment_eq {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (k : ℕ) (j : w.sourceLocations → Fin k) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    (fun s : Approximation.DistributedOperatorContraction.SampleAt
        (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) p ↦
      j ((sourceSampleEquiv w).symm s.1)) ∘ partialSlotSampleEquiv w p =
      fun i : Fin (partialSlots A w).length ↦ j (partialSlotEquiv A w i).1 := by
  classical
  intro A
  funext i
  change j ((sourceSampleEquiv w).symm
    (sourceSampleEquiv w (partialSlotEquiv A w i).1)) = _
  rw [Equiv.symm_apply_apply]

end TNLean.Lattice.PartyCircuit.SourceCircuit
