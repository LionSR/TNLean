/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Entropy.Typical.PlaneMarginalTails
import QICLean.ManyBody.Entropy.QuditRegionEntropy
import QICLean.ManyBody.Entropy.RegionEntropy
import QICLean.ManyBody.Entropy.Cut.RegionUnion
import TNLean.PEPS.AreaLaw.Polygons.Templates.TwoFamilies
import QICLean.ManyBody.Entropy.RegionStrongSubadditivity
import QICLean.ManyBody.Entropy.MovementEtaRegional
import QICLean.ManyBody.Entropy.RegionEntropyInequalities

/-!
# The numerical entropy estimate for an ordered decomposition

The two-family entropy bound and the regional dimension bound imply an entropy
estimate linear in the number of cut edges whenever the residual site count and
the sum of the mutual-information errors have linear bounds. The constants in
the conclusion are computed from those two supplied estimates.

This proves only the final numerical implication. Construction of the ordered
decomposition and derivation of its residual and information estimates remain
necessary to establish the uniform ground-state area law.

## References

OpenAI, *A two-dimensional area law from a global spectral gap* (2026), proof of
Theorem 1.1, `10-geometry.tex`, lines 846–857, immutable source
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized; no OpenAI Lean proof text is reused.

## A boundary entropy estimate from information on birth targets

For an ordered two-family partition, each retained piece is contained in a
larger birth target. A mutual-information estimate for the target against the
whole union of the exterior and the earlier pieces of the same family passes
to the retained piece by discarding part of the first system. The existing
two-family entropy cancellation then gives the boundary estimate.

The ordered partition, target information estimates, residual-size estimate
and summable scale losses are explicit premises. Their geometric construction
and uniform dependence on the Hamiltonian parameters remain separate steps.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, proof
of Theorem 1.1, `10-geometry.tex`, lines 838–852, immutable revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no OpenAI Lean proof text is reused.

## Boundary entropy from amplification-neighborhood information

Information about a birth target and the complement of its amplification
neighborhood bounds information about the whole union of the exterior and the
earlier actual pieces of the same geometric family. Discarding part of the
second system and applying the existing birth-target entropy bound gives the
boundary coefficient for the same original normalized vector.

The ordered partition, target containments, whole-union exclusion, information
estimates, residual-size bound and summable scale losses are explicit premises.
Their geometric construction and uniform dependence on the Hamiltonian
parameters remain separate steps in the full ground-state area law.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, proof
of Theorem 1.1, `10-geometry.tex`, lines 815–852, immutable revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

section

open scoped BigOperators
open ManyBody (planeDomainGraph edgeBoundary)

namespace TNLean.PEPS.AreaLaw

/-- The final numerical implication in the proof of the area law. Source:
proof of Theorem 1.1, `10-geometry.tex`, lines 846–857. The partition, its residual
site bound, and the total information-error bound are inputs; this theorem does
not assert their existence or prove the uniform ground-state area law. -/
theorem regionEntropy_le_boundary_of_partition_estimates
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (hq : 1 ≤ q)
    (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1) (A : Finset ↥Λ)
    (P : Geometry.OrderedTwoFamilyPartition A) (ε : Fin P.pieceCount → ℝ)
    (hε : ∀ i, ManyBody.regionMutualInformation Ω (P.piece i)
      (Aᶜ ∪ P.earlierSameFamily i) ≤ ε i)
    (cD cE : ℝ)
    (hD : (P.residual.card : ℝ) ≤ cD * (edgeBoundary (planeDomainGraph Λ) A).card)
    (hE : (∑ i, ε i) ≤ cE * (edgeBoundary (planeDomainGraph Λ) A).card) :
    ManyBody.regionEntropy Ω A ≤
      (cD * Real.log q + cE / 2) * (edgeBoundary (planeDomainGraph Λ) A).card := by
  have h := regionEntropy_le_residual_add_half_sum Λ q Ω hΩ A P ε hε
  have hdim := ManyBody.regionEntropy_le_card_mul_log hΩ P.residual
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hD' := mul_le_mul_of_nonneg_right hD hlog
  have hE' := mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith only [h, hdim, hD', hE']

end TNLean.PEPS.AreaLaw

end

section

open scoped BigOperators
open ManyBody (planeDomainGraph edgeBoundary)

namespace TNLean.PEPS.AreaLaw

/-- Discarding part of each birth target, followed by two-family cancellation,
turns the birth-target information estimates and the geometric scale sum into
a boundary entropy estimate. Source: proof of Theorem 1.1,
`10-geometry.tex`, lines 838–852, September 24, 2026, immutable source
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

For the source application `Y i = A ∩ T_i`. The birth targets need not be
pairwise disjoint: only their disjointness from the same-family past is used.
The partition, birth-target information bounds, residual-size bound and scale
sum are explicit premises. This statement does not construct them, prove their
uniformity, or establish the full ground-state area law. -/
theorem regionEntropy_le_boundary_of_birth_information_estimates
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (hq : 1 ≤ q)
    (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1) (A : Finset ↥Λ)
    (P : Geometry.OrderedTwoFamilyPartition A)
    (Y : Fin P.pieceCount → Finset ↥Λ)
    (hYA : ∀ i, Y i ⊆ A)
    (hXY : ∀ i, P.piece i ⊆ Y i)
    (hYpast : ∀ i, Disjoint (Y i) (P.earlierSameFamily i))
    (n : Fin P.pieceCount → ℕ)
    (cD cI cS : ℝ) (hcI : 0 ≤ cI)
    (hMI : ∀ i,
      ManyBody.regionMutualInformation Ω (Y i)
        (Aᶜ ∪ P.earlierSameFamily i) ≤ cI * (n i : ℝ) ^ (-100 : ℝ))
    (hD : (P.residual.card : ℝ) ≤ cD * (edgeBoundary (planeDomainGraph Λ) A).card)
    (hS : (∑ i, (n i : ℝ) ^ (-100 : ℝ)) ≤ cS * (edgeBoundary (planeDomainGraph Λ) A).card) :
    ManyBody.regionEntropy Ω A ≤
      (cD * Real.log q + cI * cS / 2) * (edgeBoundary (planeDomainGraph Λ) A).card := by
  exact regionEntropy_le_boundary_of_partition_estimates Λ q hq Ω hΩ A P
    (fun i ↦ cI * (n i : ℝ) ^ (-100 : ℝ))
    (fun i ↦
      (ManyBody.regionMutualInformation_mono_left (fun _ : ↥Λ ↦ Fin q) Ω
        (P.piece i) (Y i) (Aᶜ ∪ P.earlierSameFamily i) (hXY i)
        (Finset.disjoint_union_right.mpr
          ⟨disjoint_compl_right_iff.mpr (hYA i), hYpast i⟩)).trans (hMI i))
    cD (cI * cS) hD
    ((Finset.mul_sum Finset.univ (fun i ↦ (n i : ℝ) ^ (-100 : ℝ)) cI).symm.trans_le
      ((mul_le_mul_of_nonneg_left hS hcI).trans_eq
        (mul_assoc cI cS ((edgeBoundary (planeDomainGraph Λ) A).card : ℝ)).symm))

end TNLean.PEPS.AreaLaw

end

section

open scoped BigOperators
open ManyBody (planeDomainGraph edgeBoundary)

namespace TNLean.PEPS.AreaLaw

/-- Information against the complement of an amplification neighborhood controls
information against the whole union of the exterior and the same-family past.
Discarding the second system, then applying the birth-target entropy estimate,
gives the boundary bound for the same original normalized state.

Source: OpenAI, proof of Theorem 1.1, `10-geometry.tex`, lines 815–852,
immutable revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
For the source application, `Y i` is the intersection of the region with the
birth target and `N i` is the amplification neighborhood. The ordered partition,
target containments, whole-union exclusion, amplified information estimate,
residual bound and scale sum are explicit premises. This auxiliary implication
does not construct the final partition or prove those estimates. -/
theorem regionEntropy_le_boundary_of_neighborhood_information_estimates
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (hq : 1 ≤ q)
    (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1) (A : Finset ↥Λ)
    (P : Geometry.OrderedTwoFamilyPartition A)
    (Y N : Fin P.pieceCount → Finset ↥Λ)
    (hYA : ∀ i, Y i ⊆ A)
    (hXY : ∀ i, P.piece i ⊆ Y i)
    (hYN : ∀ i, Y i ⊆ N i)
    (hJ : ∀ i, Aᶜ ∪ P.earlierSameFamily i ⊆ (N i)ᶜ)
    (n : Fin P.pieceCount → ℕ)
    (cD cI cS : ℝ) (hcI : 0 ≤ cI)
    (hMI : ∀ i,
      ManyBody.regionMutualInformation Ω (Y i) (N i)ᶜ ≤
        cI * (n i : ℝ) ^ (-100 : ℝ))
    (hD : (P.residual.card : ℝ) ≤ cD * (edgeBoundary (planeDomainGraph Λ) A).card)
    (hS : (∑ i, (n i : ℝ) ^ (-100 : ℝ)) ≤ cS * (edgeBoundary (planeDomainGraph Λ) A).card) :
    ManyBody.regionEntropy Ω A ≤
      (cD * Real.log q + cI * cS / 2) * (edgeBoundary (planeDomainGraph Λ) A).card := by
  classical
  have hmono (i : Fin P.pieceCount) :
      ManyBody.regionMutualInformation Ω (Y i)
        (Aᶜ ∪ P.earlierSameFamily i) ≤
      ManyBody.regionMutualInformation Ω (Y i) (N i)ᶜ := by
    simpa only [ManyBody.regionMutualInformation, Finset.union_comm, add_comm] using
      ManyBody.regionMutualInformation_mono_left (fun _ : ↥Λ ↦ Fin q) Ω
        (Aᶜ ∪ P.earlierSameFamily i) (N i)ᶜ (Y i) (hJ i)
        (disjoint_compl_right_iff.mpr (hYN i)).symm
  exact regionEntropy_le_boundary_of_birth_information_estimates Λ q hq Ω hΩ A P
    Y hYA hXY
    (fun i ↦ (disjoint_compl_right_iff.mpr (hYN i)).mono_right
      (Finset.subset_union_right.trans (hJ i)))
    n cD cI cS hcI (fun i ↦ (hmono i).trans (hMI i)) hD hS

end TNLean.PEPS.AreaLaw

end
