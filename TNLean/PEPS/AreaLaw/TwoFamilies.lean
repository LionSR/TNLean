/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Templates
import TNLean.PEPS.AreaLaw.TheoremStatements
import QICLean.Entropy.TwoFamilies

/-!
# Ordered two-family entropy cancellation on finite lattice domains

The existing globally ordered labelled partition supplies the two induced
finite orders. This module identifies the domain model's regional entropy with
QICLean's generic finite-product entropy and applies its source-faithful bound.
No geometric construction or Hamiltonian assumption enters the argument.

## References

OpenAI, *A two-dimensional area law from a global spectral gap* (2026),
Lemma 11.1 (`geometry:cancellation`), source revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The proofs are independently written; no OpenAI Lean proof code is adapted.
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw

/-- The domain model's partial trace equals the generic finite-product reduction. -/
theorem reducedState_eq_finiteProduct (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    reducedState Λ q Ω A = FiniteProduct.reducedPure (fun _ : Site Λ ↦ Fin q) Ω A := by
  classical
  let e : ({x : Site Λ // x ∉ A} → Fin q) ≃
      FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q) Aᶜ :=
    { toFun := fun f x ↦ f ⟨x, Finset.mem_compl.mp x.property⟩
      invFun := fun f x ↦ f ⟨x, Finset.mem_compl.mpr x.property⟩
      left_inv := fun f ↦ rfl
      right_inv := fun f ↦ rfl }
  ext a b
  unfold reducedState FiniteProduct.reducedPure
  simp only [Matrix.partialTraceRight_apply, Matrix.submatrix_apply,
    FiniteProduct.reducedMatrix_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  have heq (a : {x : Site Λ // x ∈ A} → Fin q)
      (c : {x : Site Λ // x ∉ A} → Fin q) :
      (configurationSplit Λ q A).symm (a, c) =
        (FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) A).symm (a, e c) := by
    funext v
    by_cases hv : v ∈ A <;>
      simp [configurationSplit, Equiv.piEquivPiSubtypeProd, FiniteProduct.splitEquiv,
        FiniteProduct.complementEquiv, hv, e]
  simp_rw [heq]
  exact e.sum_comp (fun c ↦
    Ω ((FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) A).symm (a, c)) *
      star (Ω ((FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) A).symm (b, c))))

/-- The finite-domain regional entropy uses exactly the generic QICLean entropy. -/
theorem regionalEntropy_eq_finiteProduct (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    regionalEntropy Λ q Ω A = FiniteProduct.entropy (fun _ : Site Λ ↦ Fin q) Ω A := by
  apply vonNeumannEntropy_congr
  exact reducedState_eq_finiteProduct Λ q Ω A

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
    (hε : ∀ i, FiniteProduct.mutualInformation β ψ (P.piece i)
      (Aᶜ ∪ P.earlierSameFamily i) ≤ ε i) :
    FiniteProduct.entropy β ψ A ≤ FiniteProduct.entropy β ψ P.residual +
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
      FiniteProduct.mutualInformation β ψ (P.piece i)
        (Aᶜ ∪ Entropy.OrderedSetFunction.past P.piece (P.familyIndices f) i) ≤ ε i := by
    have hif := (Finset.mem_filter.mp hi).2
    rw [← hif, past_familyIndices]
    exact hε i
  have h := FiniteProduct.entropy_le_remainder_add_half_sum β ψ hψ A P.residual
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
theorem regionalEntropy_le_residual_add_half_sum
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) (P : Geometry.OrderedTwoFamilyPartition A)
    (ε : Fin P.pieceCount → ℝ)
    (hε : ∀ i, FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (P.piece i)
      (Aᶜ ∪ P.earlierSameFamily i) ≤ ε i) :
    regionalEntropy Λ q Ω A ≤ regionalEntropy Λ q Ω P.residual + (1 / 2) * ∑ i, ε i := by
  simp only [regionalEntropy_eq_finiteProduct]
  exact P.entropy_le_residual_add_half_sum _ Ω hΩ ε hε

end TNLean.PEPS.AreaLaw
