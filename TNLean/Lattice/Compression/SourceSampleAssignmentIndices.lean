/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceSampleIndices
import TNLean.Lattice.Compression.AllSourceSlots
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-! # Reindexing the common source-sample assignment

The original ordered source slots and the distributed gate-tagged pair samples
index the same assignments. This changes only the finite summation index.
Each endpoint space and each ordered Gaussian array remain attached to their
original source occurrence. Empty sample alphabets and empty inventories are
included without selecting an extension of an assignment.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417
and 568–579.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

open Classical in
/-- Reindex common sample assignments from ordered source slots to the actual
shared gate-pair samples. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–417 and 568–579. -/
def allSourceSampleAssignmentEquiv {a b : Layout P} (w : SourceCircuit a b) (k : ℕ) :
    (Fin (partialSlots (fun _ : P ↦ true) w).length → Fin k) ≃
      (Approximation.DistributedOperatorContraction.Sample
        (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) → Fin k) :=
  Equiv.piCongrLeft (fun _ ↦ Fin k)
    ((allSourceSlotEquiv w).trans (sourceSampleEquiv w))

open Classical in
/-- The inverse assignment reads the same sample at each original source
occurrence. It does not choose an orientation of its unordered pair.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417
and 568–579. -/
theorem allSourceSampleAssignmentEquiv_symm_apply {a b : Layout P}
    (w : SourceCircuit a b) (k : ℕ)
    (j : Approximation.DistributedOperatorContraction.Sample
      (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) → Fin k)
    (e : w.sourceLocations) :
    (allSourceSampleAssignmentEquiv w k).symm j ((allSourceSlotEquiv w).symm e) =
      j (sourceSampleEquiv w e) := by
  rw [allSourceSampleAssignmentEquiv, Equiv.piCongrLeft_symm_apply]
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]

open Classical in
/-- A matrix-valued finite sample sum is unchanged by the canonical assignment
reindexing. No restriction is imposed on the matrix summand.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 568–579. -/
theorem sum_sourceSampleAssignments_eq {a b : Layout P}
    (w : SourceCircuit a b) (k : ℕ) {m n : Type}
    (F : (Fin (partialSlots (fun _ : P ↦ true) w).length → Fin k) → Matrix m n ℂ) :
    (∑ j, F j) =
      ∑ j : Approximation.DistributedOperatorContraction.Sample
          (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) → Fin k,
        F ((allSourceSampleAssignmentEquiv w k).symm j) := by
  exact ((allSourceSampleAssignmentEquiv w k).symm.sum_comp F).symm

end TNLean.PEPS.PairEffect.SourceCircuit
