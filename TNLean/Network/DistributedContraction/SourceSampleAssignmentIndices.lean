/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Network.DistributedContraction.SourceSampleIndices
import QICLean.Circuit.Party.Compression.PartialExpansion.Sources
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import QICLean.Circuit.Party.Compression.PartialExpansion.Coefficients

/-! # Reindexing the common source-sample assignment

The original ordered source slots and the distributed gate-tagged pair samples
index the same assignments. This changes only the finite summation index.
Each endpoint space and each ordered Gaussian array remain attached to their
original source occurrence. Empty sample alphabets and empty inventories are
included without selecting an extension of an assignment.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417
and 568–579.

It also contains the following results.

* `QuantumCircuit.Party.SourceCircuit.sum_choiceSamples_eq_sum_originalGateSamples`: original gate
  labels and common samples in the same physical sum.
* `QuantumCircuit.Party.SourceCircuit.restrict_reindexedSourceSampleAssignment_eq`: restricting a
  reindexed common sample assignment.
-/

section SourceSampleAssignmentIndices

noncomputable section
namespace QuantumCircuit.Party.SourceCircuit
open TNLean.Network
variable {P : Type} [DecidableEq P]

open Classical in
/-- Reindex common sample assignments from ordered source slots to the actual
shared gate-pair samples. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–417 and 568–579. -/
def allSourceSampleAssignmentEquiv {X Y : P → Type} (w : SourceCircuit X Y) (k : ℕ) :
    (Fin (partialSlots (fun _ : P ↦ true) w).length → Fin k) ≃
      (DistributedOperatorContraction.Sample
        (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) → Fin k) :=
  Equiv.piCongrLeft (fun _ ↦ Fin k)
    ((allSourceSlotEquiv w).trans (sourceSampleEquiv w))

open Classical in
/-- The inverse assignment reads the same sample at each original source
occurrence. It does not choose an orientation of its unordered pair.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417
and 568–579. -/
theorem allSourceSampleAssignmentEquiv_symm_apply {X Y : P → Type}
    (w : SourceCircuit X Y) (k : ℕ)
    (j : DistributedOperatorContraction.Sample
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
theorem sum_sourceSampleAssignments_eq {X Y : P → Type}
    (w : SourceCircuit X Y) (k : ℕ) {m n : Type}
    (F : (Fin (partialSlots (fun _ : P ↦ true) w).length → Fin k) → Matrix m n ℂ) :
    (∑ j, F j) =
      ∑ j : DistributedOperatorContraction.Sample
          (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) → Fin k,
        F ((allSourceSampleAssignmentEquiv w k).symm j) := by
  exact ((allSourceSampleAssignmentEquiv w k).symm.sum_comp F).symm

end QuantumCircuit.Party.SourceCircuit

end

end SourceSampleAssignmentIndices

section JointSourceSumReindex

/-! # Original gate labels and common samples in the same physical sum

The ket and bra labels are reindexed independently by their original gate
occurrences. The common sample assignment is reindexed once. This identity
changes only the finite summation indices; its matrix summand is arbitrary.
The original empty-gate scalar is not part of the branch coefficient product.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381
and 565–579.
-/

noncomputable section
open scoped ComplexConjugate
namespace QuantumCircuit.Party.SourceCircuit
open TNLean.Network
variable {P : Type} [DecidableEq P]

open Classical in
/-- Reindex the two chronological branch choices and their shared samples in
an arbitrary matrix-valued sum. The original occurrence tags and inverse
assignments are retained. No extension of a local assignment is selected.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381
and 565–579. -/
theorem sum_choiceSamples_eq_sum_originalGateSamples {X Y : P → Type}
    (w : SourceCircuit X Y) (k : ℕ) {m n : Type}
    (K : Choices (fun _ : P ↦ true) w → Choices (fun _ : P ↦ true) w →
      (Fin (partialSlots (fun _ : P ↦ true) w).length → Fin k) → Matrix m n ℂ) :
    (∑ ξ, ∑ ζ, (coefficient (fun _ : P ↦ true) w ξ *
        conj (coefficient (fun _ : P ↦ true) w ζ)) • ∑ j, K ξ ζ j) =
      ∑ η : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
        ∑ θ : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
          (∏ g : w.nonemptyGateLocations,
            w.branchCoefficient g.1 (η g) * conj (w.branchCoefficient g.1 (θ g))) •
              ∑ j : DistributedOperatorContraction.Sample
                  (Finset.univ : Finset w.nonemptyGateLocations)
                  (fun g ↦ w.participants g.1) → Fin k,
                K ((allChoicesNonemptyLabelsEquiv w).symm η)
                  ((allChoicesNonemptyLabelsEquiv w).symm θ)
                  ((allSourceSampleAssignmentEquiv w k).symm j) := by
  rw [sum_coefficient_all_mul_conj_smul_eq_sum_nonemptyGateLabels
    w (fun ξ ζ ↦ ∑ j, K ξ ζ j)]
  simp_rw [sum_sourceSampleAssignments_eq]

end QuantumCircuit.Party.SourceCircuit

end

end JointSourceSumReindex

section ReindexedLocalSourceSamples

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

end

end ReindexedLocalSourceSamples
