/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Polygons.Templates.Templates
import TNLean.PEPS.AreaLaw.Polygons.Squares.CellCounting
import TNLean.PEPS.AreaLaw.Collar.AmbientDepth
import TNLean.PEPS.AreaLaw.Collar.Scales.Exponents
import QICLean.ManyBody.Entropy.RegionEntropy
import QICLean.ManyBody.Entropy.TwoFamilies

/-!
# Ordered two-family entropy cancellation on finite lattice domains

The existing globally ordered labelled partition supplies the two induced
finite orders. This module applies QICLean's source-faithful bound to the regional
entropy `ManyBody.regionEntropy` of the domain model.
No geometric construction or Hamiltonian assumption enters the argument.

The module also states Proposition 11.2 (`prop:two-families`) as the predicate
`TwoFamilyDecomposition`: every cut has an ordered two-family partition whose pieces lie in
separated templates. It is proved in `BirthRegions/FinalRegions/TwoFamilyAssembly`.

## References

OpenAI, *A two-dimensional area law from a global spectral gap* (2026),
Lemma 11.1 (`geometry:cancellation`) and Proposition 11.2 (`prop:two-families`),
`10-geometry.tex` lines 98–140, source revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The proofs are independently written; no OpenAI Lean proof code is adapted.
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw

namespace Geometry.OrderedTwoFamilyPartition

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-- The indices with one of the two labels, carrying the original order. -/
def familyIndices (P : OrderedTwoFamilyPartition A) (f : Fin 2) : Finset (Fin P.pieceCount) :=
  Finset.univ.filter fun i ↦ P.family i = f

/-- The induced family order has precisely the previously specified same-family
past; no independent enumeration changes the conditioning subsystem. -/
theorem past_familyIndices (P : OrderedTwoFamilyPartition A) (i : Fin P.pieceCount) :
    Entropy.OrderedSetFunction.past P.piece (P.familyIndices (P.family i)) i =
      P.earlierSameFamily i := by
  simp only [Entropy.OrderedSetFunction.past, familyIndices, earlierSameFamily,
    Finset.filter_filter, and_comm]

/-- The two labelled families exhaust the original common index set. -/
theorem union_familyIndices (P : OrderedTwoFamilyPartition A) :
    P.familyIndices 0 ∪ P.familyIndices 1 = Finset.univ := by
  ext i
  simp only [familyIndices, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, iff_true]
  omega

variable [Fintype ι]

/-- QICLean's exact two-family bound for the existing labelled decomposition.
The estimate for each piece uses the entire exterior-plus-past subsystem. -/
theorem entropy_le_residual_add_half_sum (P : OrderedTwoFamilyPartition A)
    (β : ι → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : ι) → β v)) (hψ : ‖ψ‖ = 1)
    (ε : Fin P.pieceCount → ℝ)
    (hε : ∀ i, ManyBody.regionMutualInformation ψ (P.piece i)
      (Aᶜ ∪ P.earlierSameFamily i) ≤ ε i) :
    ManyBody.regionEntropy ψ A ≤ ManyBody.regionEntropy ψ P.residual +
      (1 / 2) * ∑ i, ε i := by
  classical
  have hcover : A = P.residual ∪ (P.familyIndices 0).biUnion P.piece ∪
      (P.familyIndices 1).biUnion P.piece := by
    rw [Finset.union_assoc, ← Finset.union_biUnion, union_familyIndices]
    exact P.cover
  have hfamily (f : Fin 2) :
      ((P.familyIndices f : Finset _) : Set _).PairwiseDisjoint P.piece := by
    intro i hi j hj hij
    exact P.disjoint i j hij
  have hcross : ∀ i ∈ P.familyIndices 0, ∀ j ∈ P.familyIndices 1,
      Disjoint (P.piece i) (P.piece j) := by
    intro i hi j hj
    apply P.disjoint i j
    have hi0 := (Finset.mem_filter.mp hi).2
    have hj1 := (Finset.mem_filter.mp hj).2
    intro hij
    subst j
    rw [hi0] at hj1
    exact Fin.zero_ne_one hj1
  have hbound (f : Fin 2) (i : Fin P.pieceCount) (hi : i ∈ P.familyIndices f) :
      ManyBody.regionMutualInformation ψ (P.piece i)
        (Aᶜ ∪ Entropy.OrderedSetFunction.past P.piece (P.familyIndices f) i) ≤ ε i := by
    have hif := (Finset.mem_filter.mp hi).2
    rw [← hif, past_familyIndices]
    exact hε i
  have h := ManyBody.regionEntropy_le_remainder_add_half_sum β ψ hψ A P.residual
    P.piece (P.familyIndices 0) P.piece (P.familyIndices 1) hcover
    (fun i _ ↦ P.residual_disjoint i) (fun i _ ↦ P.residual_disjoint i)
    (hfamily 0) (hfamily 1) hcross ε ε (hbound 0) (hbound 1)
  have hdisj : Disjoint (P.familyIndices 0) (P.familyIndices 1) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi0 := (Finset.mem_filter.mp hi).2
    have hi1 := (Finset.mem_filter.mp hj).2
    omega
  rwa [← Finset.sum_union hdisj, union_familyIndices] at h

end Geometry.OrderedTwoFamilyPartition

/-- The physical finite-domain specialization of OpenAI's Lemma 11.1 using the
model's existing regional entropy. -/
theorem regionEntropy_le_residual_add_half_sum
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1)
    (A : Finset ↥Λ) (P : Geometry.OrderedTwoFamilyPartition A)
    (ε : Fin P.pieceCount → ℝ)
    (hε : ∀ i, ManyBody.regionMutualInformation Ω (P.piece i)
      (Aᶜ ∪ P.earlierSameFamily i) ≤ ε i) :
    ManyBody.regionEntropy Ω A ≤ ManyBody.regionEntropy Ω P.residual + (1 / 2) * ∑ i, ε i := by
  exact P.entropy_le_residual_add_half_sum _ Ω hΩ ε hε

section TwoFamilyDecomposition

open ManyBody (planeDomainGraph edgeBoundary)

/-- **Proposition 11.2** (`prop:two-families`, `10-geometry.tex` lines 98–140),
for the template constants `D₀, Ctpl` of Definition 9.3. For every lower scale
threshold `n_* ≥ 1` there is a constant `C` such that every cut `A` of a finite
induced domain with `b = |∂_Λ A| > 0` has an ordered partition
`A = D ∪ ⋃ᵢ Xᵢ` into two labelled families of nonempty pieces, with templates
`Tᵢ` of parameters `(nᵢ, sᵢ)` separated from the cut endpoints `Z`, such that
`|D| ≤ C b`, `Xᵢ ⊆ A ∩ Tᵢ`, `⌊nᵢ^(1-ℓ)⌋ ≤ sᵢ`, `nᵢ ≥ n_*`, the clearances
`dist_∞(Tᵢ, Z) > 2 nᵢ^β` and `dist_∞(Tᵢ, ⋃_{j<i, fⱼ=fᵢ} Xⱼ) > 2 nᵢ^β` hold, and
`∑ᵢ nᵢ^(-100) ≤ C b`. The constant is chosen before the domain and the cut. -/
def TwoFamilyDecomposition (D₀ Ctpl : ℝ) : Prop :=
  ∀ nstar : ℕ, 1 ≤ nstar → ∃ C : ℝ,
    ∀ Λ : Finset (ℤ × ℤ), ∀ A : Finset ↥Λ, 0 < (edgeBoundary (planeDomainGraph Λ) A).card →
      ∃ P : Geometry.OrderedTwoFamilyPartition A, ∃ n s : Fin P.pieceCount → ℕ,
        ∃ T : ∀ i, Geometry.Template Ctpl (n i) (s i),
          (P.residual.card : ℝ) ≤ C * (edgeBoundary (planeDomainGraph Λ) A).card ∧
          (∀ i, (P.piece i).Nonempty) ∧
          (∀ i, P.piece i ⊆ A.filter fun x ↦ x.val ∈ (T i).points) ∧
          (∀ i, (T i).IsSeparated D₀ (Geometry.boundaryEndpoints Λ A)) ∧
          (∀ i, ⌊(n i : ℝ) ^ (1 - (Exponents.geometryEll : ℝ))⌋₊ ≤ s i) ∧
          (∀ i, nstar ≤ n i) ∧
          (∀ i, ∀ t ∈ (T i).points, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
            2 * (n i : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t z : ℝ)) ∧
          (∀ i, ∀ t ∈ (T i).points, ∀ x ∈ P.earlierSameFamily i,
            2 * (n i : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t x.val : ℝ)) ∧
          ∑ i, ((n i : ℝ) ^ 100)⁻¹ ≤ C * (edgeBoundary (planeDomainGraph Λ) A).card

end TwoFamilyDecomposition

end TNLean.PEPS.AreaLaw
