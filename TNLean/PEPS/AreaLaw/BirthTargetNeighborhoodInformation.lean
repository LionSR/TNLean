/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.BirthTargetEntropy

/-!
# Boundary entropy from amplification-neighborhood information

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

open scoped BigOperators

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
theorem regionalEntropy_le_boundary_of_neighborhood_information_estimates
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (hq : 1 ≤ q)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ))
    (P : Geometry.OrderedTwoFamilyPartition A)
    (Y N : Fin P.pieceCount → Finset (Site Λ))
    (hYA : ∀ i, Y i ⊆ A)
    (hXY : ∀ i, P.piece i ⊆ Y i)
    (hYN : ∀ i, Y i ⊆ N i)
    (hJ : ∀ i, Aᶜ ∪ P.earlierSameFamily i ⊆ (N i)ᶜ)
    (n : Fin P.pieceCount → ℕ)
    (cD cI cS : ℝ) (hcI : 0 ≤ cI)
    (hMI : ∀ i,
      FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (Y i) (N i)ᶜ ≤
        cI * (n i : ℝ) ^ (-100 : ℝ))
    (hD : (P.residual.card : ℝ) ≤ cD * (edgeBoundary Λ A).card)
    (hS : (∑ i, (n i : ℝ) ^ (-100 : ℝ)) ≤ cS * (edgeBoundary Λ A).card) :
    regionalEntropy Λ q Ω A ≤
      (cD * Real.log q + cI * cS / 2) * (edgeBoundary Λ A).card := by
  classical
  have hmono (i : Fin P.pieceCount) :
      FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (Y i)
        (Aᶜ ∪ P.earlierSameFamily i) ≤
      FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (Y i) (N i)ᶜ := by
    simpa only [FiniteProduct.mutualInformation, Finset.union_comm, add_comm] using
      FiniteProduct.mutualInformation_mono_left (fun _ : Site Λ ↦ Fin q) Ω
        (Aᶜ ∪ P.earlierSameFamily i) (N i)ᶜ (Y i) (hJ i)
        (disjoint_compl_right_iff.mpr (hYN i)).symm
  exact regionalEntropy_le_boundary_of_birth_information_estimates Λ q hq Ω hΩ A P
    Y hYA hXY
    (fun i ↦ (disjoint_compl_right_iff.mpr (hYN i)).mono_right
      (Finset.subset_union_right.trans (hJ i)))
    n cD cI cS hcI (fun i ↦ (hmono i).trans (hMI i)) hD hS

end TNLean.PEPS.AreaLaw
