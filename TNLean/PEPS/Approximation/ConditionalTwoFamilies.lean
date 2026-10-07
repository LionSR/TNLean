/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TwoFamilies
import QICLean.Entropy.ConditionalTwoFamilies

/-!
# Labelled conditional two-family entropy estimates

The existing ordered two-family partition supplies both induced family orders.
The second exterior is the complement of the region and original conditioner,
as in the source's forbidden-color-one convention. A finite-domain corollary is
stated directly with the four already-defined regional entropies. No new state,
partition, or conditional-information definition is introduced here.

This is the entropy step in the proof of OpenAI's PEPS cell-information lemma,
September 24, 2026, Lemma 3.2, `eq:info-tile-cost`. It does not prove the cell's
geometric decomposition or its polylogarithmic counting estimate. These proofs
are independently written; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/
build/sections/02-information.tex
Labels: eq:info-tile-cost.
Provenance-ID: 8765-tn-conditional-01
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition.conditionalMutualInformation_le_sum
Provenance-ID: 8765-tn-conditional-02
Downstream declaration:
TNLean.PEPS.AreaLaw.regionalEntropy_conditional_le_residual_add_sum
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Finset V}

/-- The conditional two-family bound for the existing globally ordered labelled
partition. The two whole-union estimates use the original and opposite exteriors. -/
theorem conditionalMutualInformation_le_sum
    (P : OrderedTwoFamilyPartition G)
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (B C : Finset V) (hGB : Disjoint G B) (hGC : Disjoint G C) (hBC : Disjoint B C)
    (ε : Fin P.pieceCount → ℝ)
    (h₀ : ∀ i, P.family i = 0 → FiniteProduct.mutualInformation β ψ (P.piece i)
      (C ∪ B ∪ P.earlierSameFamily i) ≤ ε i)
    (h₁ : ∀ i, P.family i = 1 → FiniteProduct.mutualInformation β ψ (P.piece i)
      ((G ∪ B)ᶜ ∪ P.earlierSameFamily i) ≤ ε i) :
    FiniteProduct.conditionalMutualInformation β ψ G C B ≤
      2 * FiniteProduct.entropy β ψ P.residual + ∑ i, ε i := by
  classical
  have hcover : G = P.residual ∪ (P.familyIndices 0).biUnion P.piece ∪
      (P.familyIndices 1).biUnion P.piece := by
    rw [Finset.union_assoc, ← Finset.union_biUnion, P.union_familyIndices]
    exact P.cover
  have hfamily (f : Fin 2) :
      ((P.familyIndices f : Finset _) : Set _).PairwiseDisjoint P.piece := by
    intro i _ j _ hij
    exact P.disjoint i j hij
  have hlabels : Disjoint (P.familyIndices 0) (P.familyIndices 1) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Fin.zero_ne_one ((Finset.mem_filter.mp hi).2.symm.trans
      (Finset.mem_filter.mp hj).2)
  have hcross : ∀ i ∈ P.familyIndices 0, ∀ j ∈ P.familyIndices 1,
      Disjoint (P.piece i) (P.piece j) := by
    intro i hi j hj
    exact P.disjoint i j (fun hij ↦ Finset.disjoint_left.mp hlabels (hij ▸ hi) hj)
  have h := FiniteProduct.conditionalMutualInformation_le_two_family_sum β ψ hψ
    G B C P.residual P.piece (P.familyIndices 0) P.piece (P.familyIndices 1)
    hcover hGB hGC hBC (fun i _ ↦ P.residual_disjoint i)
    (fun i _ ↦ P.residual_disjoint i) (hfamily 0) (hfamily 1) hcross ε ε (by
      intro i hi
      have hi₀ := (Finset.mem_filter.mp hi).2
      have hpast := P.past_familyIndices i
      rw [hi₀] at hpast
      rw [hpast]
      exact h₀ i hi₀) (by
      intro i hi
      have hi₁ := (Finset.mem_filter.mp hi).2
      have hpast := P.past_familyIndices i
      rw [hi₁] at hpast
      rw [FiniteProduct.target_union_complement_eq_exterior G B C hGC hBC, hpast]
      exact h₁ i hi₁)
  have hsum := Finset.sum_union hlabels (f := ε)
  rw [P.union_familyIndices] at hsum
  linarith only [h, hsum]

end TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition

namespace TNLean.PEPS.AreaLaw

/-- The source conditional-information bound written with the four native
regional entropy terms. Canonical tripartite CMI identification is separate;
this theorem uses only the existing model entropy and its proved QICLean equality. -/
theorem regionalEntropy_conditional_le_residual_add_sum
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (G B C : Finset (Site Λ)) (P : Geometry.OrderedTwoFamilyPartition G)
    (hGB : Disjoint G B) (hGC : Disjoint G C) (hBC : Disjoint B C)
    (ε : Fin P.pieceCount → ℝ)
    (h₀ : ∀ i, P.family i = 0 →
      FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (P.piece i)
        (C ∪ B ∪ P.earlierSameFamily i) ≤ ε i)
    (h₁ : ∀ i, P.family i = 1 →
      FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (P.piece i)
        ((G ∪ B)ᶜ ∪ P.earlierSameFamily i) ≤ ε i) :
    regionalEntropy Λ q Ω (G ∪ B) + regionalEntropy Λ q Ω (C ∪ B) -
        regionalEntropy Λ q Ω B - regionalEntropy Λ q Ω (G ∪ C ∪ B) ≤
      2 * regionalEntropy Λ q Ω P.residual + ∑ i, ε i := by
  simp only [regionalEntropy_eq_finiteProduct]
  exact P.conditionalMutualInformation_le_sum _ Ω hΩ B C hGB hGC hBC ε h₀ h₁

end TNLean.PEPS.AreaLaw
