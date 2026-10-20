/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.PointwiseChoiceCoefficient
import TNLean.Lattice.Compression.SourceSampleAssignmentIndices

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
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

open Classical in
/-- Reindex the two chronological branch choices and their shared samples in
an arbitrary matrix-valued sum. The original occurrence tags and inverse
assignments are retained. No extension of a local assignment is selected.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381
and 565–579. -/
theorem sum_choiceSamples_eq_sum_originalGateSamples {a b : Layout P}
    (w : SourceCircuit a b) (k : ℕ) {m n : Type}
    (K : Choices (fun _ : P ↦ true) w → Choices (fun _ : P ↦ true) w →
      (Fin (partialSlots (fun _ : P ↦ true) w).length → Fin k) → Matrix m n ℂ) :
    (∑ ξ, ∑ ζ, (coefficient (fun _ : P ↦ true) w ξ *
        conj (coefficient (fun _ : P ↦ true) w ζ)) • ∑ j, K ξ ζ j) =
      ∑ η : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
        ∑ θ : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
          (∏ g : w.nonemptyGateLocations,
            w.branchCoefficient g.1 (η g) * conj (w.branchCoefficient g.1 (θ g))) •
              ∑ j : Approximation.DistributedOperatorContraction.Sample
                  (Finset.univ : Finset w.nonemptyGateLocations)
                  (fun g ↦ w.participants g.1) → Fin k,
                K ((allChoicesNonemptyLabelsEquiv w).symm η)
                  ((allChoicesNonemptyLabelsEquiv w).symm θ)
                  ((allSourceSampleAssignmentEquiv w k).symm j) := by
  rw [sum_coefficient_all_mul_conj_smul_eq_sum_nonemptyGateLabels
    w (fun ξ ζ ↦ ∑ j, K ξ ζ j)]
  simp_rw [sum_sourceSampleAssignments_eq]

end TNLean.PEPS.PairEffect.SourceCircuit
