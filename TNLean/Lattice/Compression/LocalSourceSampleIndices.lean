/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceSampleIndices
import TNLean.Lattice.Compression.PartialSourcePreparation
import TNLean.Lattice.Compression.IncidentGateLabels

/-!
# Local sample indices in the original source order

The selected source-slot indices at one party are exactly the sample positions
incident to that party. This correspondence retains the original occurrence
and the original ordering of selected source slots. Consequently, a local
sample assignment requires values only at these positions, including when
an unrelated source has an empty sample alphabet.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
342–417 and 568–579.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation
variable {P : Type}

open Classical in
/-- Incidence of a sample pair is exactly incidence of its original two
source endpoints. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 342–364 and 568–579. -/
theorem mem_sourceSampleEquiv_iff {a b : Layout P} (w : SourceCircuit a b)
    (p : P) (e : w.sourceLocations) :
    p ∈ (sourceSampleEquiv w e).2.1.toFinset ↔
      (w.endpoints e).1 = p ∨ (w.endpoints e).2 = p := by
  change p ∈ (sourcePairEquiv w e.1 e.2).1.toFinset ↔
    (w.endpoints e).1 = p ∨ (w.endpoints e).2 = p
  rw [sourcePairEquiv_apply]
  simp only [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton, eq_comm]

open Classical in
/-- The ordered singleton source slots are precisely the local sample indices
of the distributed contraction. No sample value at another source position
is chosen. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 253–267, 383–417 and 568–579. -/
def partialSlotSampleEquiv {a b : Layout P} (w : SourceCircuit a b) (p : P) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    Fin (partialSlots A w).length ≃ Approximation.DistributedOperatorContraction.SampleAt
      (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) p := by
  intro A
  refine (partialSlotEquiv A w).trans ((sourceSampleEquiv w).subtypeEquiv ?_)
  intro e
  rw [mem_sourceSampleEquiv_iff]
  dsimp only [A]
  simp_rw [partySelector_affectedOwner_all_apply]
  simp only [partySelector, decide_eq_true_eq]

end TNLean.PEPS.PairEffect.SourceCircuit
