/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.FiniteProduct
import QICLean.Analysis.EntropyDecomposition

/-!
# Regional entropies after relabelling sites and adjoining systems

The final entropy comparison of the amplification proof is carried out on the physical
sites enlarged by two ancillary copies of the target. It uses two facts about regional
entropies of finite-product pure states, proved here for an arbitrary finite local
alphabet `F`:

* relabelling the sites along a bijection `σ` moves every regional entropy along `σ`;
* for a product `f ⊗ g` of unit vectors on the sites `A ⊕ B`, the entropy of a region
  `R ⊔ T` with `R ⊆ A` and `T ⊆ B` is the sum of the entropies of `R` for `f` and of `T`
  for `g`.

Consequently mutual information between two regions of `A` is unchanged by adjoining the
sites `B` in a product state, and a region of `B` has no mutual information with a region
of `A`.

## Main definitions

* `FiniteProduct.relabelSites`: a vector moved along a bijection of the sites.
* `FiniteProduct.sumSitesProduct`: the product vector `f ⊗ g` on the sites `A ⊕ B`.

## Main statements

* `FiniteProduct.entropy_relabelSites`, `FiniteProduct.mutualInformation_relabelSites`.
* `FiniteProduct.entropy_sumSitesProduct`, `FiniteProduct.mutualInformation_sumSitesProduct_inl`,
  `FiniteProduct.mutualInformation_sumSitesProduct_inr_inl`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 342–347
  and 547–553: the joint reduction of `e'` and a remote set in `φ` is the original
  reduction of the target and the remote set, relabelled, and in `η` it is a product.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace FiniteProduct

variable {F : Type*} [Fintype F] [DecidableEq F]

section Relabel

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- A vector on the configurations of `W`, read on `V` through a bijection `σ : V ≃ W`. -/
noncomputable def relabelSites (σ : V ≃ W) (ψ : EuclideanSpace ℂ (W → F)) :
    EuclideanSpace ℂ (V → F) :=
  WithLp.toLp 2 fun c => ψ (c ∘ σ.symm)

/-- Configurations of a region, moved along a bijection of the sites. -/
def regionRelabel (σ : V ≃ W) (S : Finset V) :
    Configuration (fun _ : V => F) S ≃ Configuration (fun _ : W => F) (S.map σ.toEmbedding) :=
  Equiv.arrowCongr (σ.subtypeEquiv fun v => by simp) (Equiv.refl F)

/-- Configurations of the complement of a region, moved along a bijection of the sites. -/
def complRelabel (σ : V ≃ W) (S : Finset V) :
    Configuration (fun _ : V => F) Sᶜ ≃
      Configuration (fun _ : W => F) (S.map σ.toEmbedding)ᶜ :=
  Equiv.arrowCongr (σ.subtypeEquiv fun v => by simp) (Equiv.refl F)

omit [Fintype F] [DecidableEq F] in
theorem splitEquiv_symm_comp_relabel (σ : V ≃ W) (S : Finset V)
    (a : Configuration (fun _ : V => F) S) (d : Configuration (fun _ : V => F) Sᶜ) :
    (splitEquiv (fun _ : V => F) S).symm (a, d) ∘ σ.symm =
      (splitEquiv (fun _ : W => F) (S.map σ.toEmbedding)).symm
        (regionRelabel σ S a, complRelabel σ S d) := by
  funext w
  by_cases hw : w ∈ S.map σ.toEmbedding
  · have hv : σ.symm w ∈ S := Finset.mem_map_equiv.mp hw
    rw [Function.comp_apply, splitEquiv_symm_apply_of_mem _ _ _ _ _ hv,
      splitEquiv_symm_apply_of_mem _ _ _ _ _ hw]
    rfl
  · have hv : σ.symm w ∉ S := fun h => hw (Finset.mem_map_equiv.mpr h)
    rw [Function.comp_apply, splitEquiv_symm_apply_of_notMem _ _ _ _ _ hv,
      splitEquiv_symm_apply_of_notMem _ _ _ _ _ hw]
    rfl

omit [DecidableEq F] in
/-- The reduced state of a relabelled vector is the reduced state of the original vector
on the image region. -/
theorem reducedPure_relabelSites (σ : V ≃ W) (ψ : EuclideanSpace ℂ (W → F)) (S : Finset V) :
    reducedPure (fun _ : V => F) (relabelSites σ ψ) S =
      (reducedPure (fun _ : W => F) ψ (S.map σ.toEmbedding)).submatrix
        (regionRelabel σ S) (regionRelabel σ S) := by
  ext a b
  simp only [reducedPure, reducedMatrix_apply, submatrix_apply, vecMulVec_apply,
    Pi.star_apply, relabelSites]
  simp_rw [splitEquiv_symm_comp_relabel]
  exact (complRelabel σ S).sum_comp (fun d => ψ ((splitEquiv (fun _ : W => F)
    (S.map σ.toEmbedding)).symm (regionRelabel σ S a, d)) *
      star (ψ ((splitEquiv (fun _ : W => F) (S.map σ.toEmbedding)).symm
        (regionRelabel σ S b, d))))

/-- **Relabelling sites moves regional entropies.** -/
theorem entropy_relabelSites (σ : V ≃ W) (ψ : EuclideanSpace ℂ (W → F)) (S : Finset V) :
    entropy (fun _ : V => F) (relabelSites σ ψ) S =
      entropy (fun _ : W => F) ψ (S.map σ.toEmbedding) := by
  unfold entropy
  rw [vonNeumannEntropy_congr (reducedPure_relabelSites σ ψ S) _
    (((reducedPure_posSemidef _ ψ _).submatrix _).isHermitian)]
  exact vonNeumannEntropy_submatrix_equiv _ _ _

/-- **Relabelling sites moves mutual information.** -/
theorem mutualInformation_relabelSites (σ : V ≃ W) (ψ : EuclideanSpace ℂ (W → F))
    (R T : Finset V) :
    mutualInformation (fun _ : V => F) (relabelSites σ ψ) R T =
      mutualInformation (fun _ : W => F) ψ (R.map σ.toEmbedding) (T.map σ.toEmbedding) := by
  simp only [mutualInformation, entropy_relabelSites, Finset.map_union]

end Relabel

section Sum

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The product vector `f ⊗ g` on the sites `A ⊕ B`. -/
noncomputable def sumSitesProduct (f : EuclideanSpace ℂ (A → F)) (g : EuclideanSpace ℂ (B → F)) :
    EuclideanSpace ℂ (A ⊕ B → F) :=
  WithLp.toLp 2 fun c => f (c ∘ Sum.inl) * g (c ∘ Sum.inr)

/-- Configurations of a region `R ⊔ T` of `A ⊕ B` as pairs of configurations. -/
def disjSumRegionEquiv (R : Finset A) (T : Finset B) :
    Configuration (fun _ : A ⊕ B => F) (R.disjSum T) ≃
      Configuration (fun _ : A => F) R × Configuration (fun _ : B => F) T :=
  (Equiv.arrowCongr (Equiv.subtypeSum.trans (Equiv.sumCongr
    (Equiv.subtypeEquivRight fun _ => Finset.inl_mem_disjSum)
    (Equiv.subtypeEquivRight fun _ => Finset.inr_mem_disjSum))) (Equiv.refl F)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- Configurations of the complement of `R ⊔ T` as pairs of configurations. -/
def disjSumComplEquiv (R : Finset A) (T : Finset B) :
    Configuration (fun _ : A ⊕ B => F) (R.disjSum T)ᶜ ≃
      Configuration (fun _ : A => F) Rᶜ × Configuration (fun _ : B => F) Tᶜ :=
  (Equiv.arrowCongr (Equiv.subtypeSum.trans (Equiv.sumCongr
    (Equiv.subtypeEquivRight fun _ => by simp)
    (Equiv.subtypeEquivRight fun _ => by simp))) (Equiv.refl F)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

omit [Fintype F] [DecidableEq F] in
theorem splitEquiv_symm_comp_inl (R : Finset A) (T : Finset B)
    (a : Configuration (fun _ : A ⊕ B => F) (R.disjSum T))
    (d : Configuration (fun _ : A ⊕ B => F) (R.disjSum T)ᶜ) :
    (splitEquiv (fun _ : A ⊕ B => F) (R.disjSum T)).symm (a, d) ∘ Sum.inl =
      (splitEquiv (fun _ : A => F) R).symm
        ((disjSumRegionEquiv R T a).1, (disjSumComplEquiv R T d).1) := by
  funext x
  by_cases hx : x ∈ R
  · rw [Function.comp_apply, splitEquiv_symm_apply_of_mem _ _ _ _ _
      (Finset.inl_mem_disjSum.mpr hx), splitEquiv_symm_apply_of_mem _ _ _ _ _ hx]
    rfl
  · rw [Function.comp_apply, splitEquiv_symm_apply_of_notMem _ _ _ _ _
      (fun h => hx (Finset.inl_mem_disjSum.mp h)), splitEquiv_symm_apply_of_notMem _ _ _ _ _ hx]
    rfl

omit [Fintype F] [DecidableEq F] in
theorem splitEquiv_symm_comp_inr (R : Finset A) (T : Finset B)
    (a : Configuration (fun _ : A ⊕ B => F) (R.disjSum T))
    (d : Configuration (fun _ : A ⊕ B => F) (R.disjSum T)ᶜ) :
    (splitEquiv (fun _ : A ⊕ B => F) (R.disjSum T)).symm (a, d) ∘ Sum.inr =
      (splitEquiv (fun _ : B => F) T).symm
        ((disjSumRegionEquiv R T a).2, (disjSumComplEquiv R T d).2) := by
  funext x
  by_cases hx : x ∈ T
  · rw [Function.comp_apply, splitEquiv_symm_apply_of_mem _ _ _ _ _
      (Finset.inr_mem_disjSum.mpr hx), splitEquiv_symm_apply_of_mem _ _ _ _ _ hx]
    rfl
  · rw [Function.comp_apply, splitEquiv_symm_apply_of_notMem _ _ _ _ _
      (fun h => hx (Finset.inr_mem_disjSum.mp h)), splitEquiv_symm_apply_of_notMem _ _ _ _ _ hx]
    rfl

omit [DecidableEq F] in
/-- The reduced state of a product vector on `R ⊔ T` is the Kronecker product of the
reduced states of the two factors. -/
theorem reducedPure_sumSitesProduct (f : EuclideanSpace ℂ (A → F))
    (g : EuclideanSpace ℂ (B → F)) (R : Finset A) (T : Finset B) :
    reducedPure (fun _ : A ⊕ B => F) (sumSitesProduct f g) (R.disjSum T) =
      (reducedPure (fun _ : A => F) f R ⊗ₖ reducedPure (fun _ : B => F) g T).submatrix
        (disjSumRegionEquiv R T) (disjSumRegionEquiv R T) := by
  ext a b
  simp only [reducedPure, reducedMatrix_apply, submatrix_apply, kroneckerMap_apply,
    vecMulVec_apply, Pi.star_apply, sumSitesProduct]
  rw [← (disjSumComplEquiv R T).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
  rw [splitEquiv_symm_comp_inl, splitEquiv_symm_comp_inl, splitEquiv_symm_comp_inr,
    splitEquiv_symm_comp_inr]
  simp only [Equiv.apply_symm_apply, star_mul]
  ring

/-- **Entropy of a region of a product vector.** For unit vectors `f` on the sites `A` and
`g` on the sites `B`, the region `R ⊔ T` of `f ⊗ g` has entropy `S_f(R) + S_g(T)`. -/
theorem entropy_sumSitesProduct {f : EuclideanSpace ℂ (A → F)} {g : EuclideanSpace ℂ (B → F)}
    (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (R : Finset A) (T : Finset B) :
    entropy (fun _ : A ⊕ B => F) (sumSitesProduct f g) (R.disjSum T) =
      entropy (fun _ : A => F) f R + entropy (fun _ : B => F) g T := by
  unfold entropy
  have hR := reducedPure_posSemidef (fun _ : A => F) f R
  have hT := reducedPure_posSemidef (fun _ : B => F) g T
  rw [vonNeumannEntropy_congr (reducedPure_sumSitesProduct f g R T) _
    (((hR.kronecker hT).submatrix _).isHermitian),
    vonNeumannEntropy_submatrix_equiv _ _ (hR.kronecker hT).isHermitian]
  exact vonNeumannEntropy_kronecker hR hT (trace_reducedPure _ f hf R)
    (trace_reducedPure _ g hg T)

/-- **Adjoining sites in a product state** does not change the mutual information of two
regions of `A`. -/
theorem mutualInformation_sumSitesProduct_inl {f : EuclideanSpace ℂ (A → F)}
    {g : EuclideanSpace ℂ (B → F)} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (R T : Finset A) :
    mutualInformation (fun _ : A ⊕ B => F) (sumSitesProduct f g) (R.disjSum ∅)
        (T.disjSum ∅) = mutualInformation (fun _ : A => F) f R T := by
  have hunion : R.disjSum (∅ : Finset B) ∪ T.disjSum ∅ = (R ∪ T).disjSum ∅ := by
    ext x
    rcases x with x | x <;> simp
  simp only [mutualInformation, hunion, entropy_sumSitesProduct hf hg, entropy_empty _ g hg,
    add_zero]

/-- **A region of the adjoined sites** has no mutual information with a region of `A` in a
product vector. -/
theorem mutualInformation_sumSitesProduct_inr_inl {f : EuclideanSpace ℂ (A → F)}
    {g : EuclideanSpace ℂ (B → F)} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (T : Finset B)
    (R : Finset A) :
    mutualInformation (fun _ : A ⊕ B => F) (sumSitesProduct f g) ((∅ : Finset A).disjSum T)
        (R.disjSum ∅) = 0 := by
  have hunion : (∅ : Finset A).disjSum T ∪ R.disjSum ∅ = R.disjSum T := by
    ext x
    rcases x with x | x <;> simp
  simp only [mutualInformation, hunion, entropy_sumSitesProduct hf hg, entropy_empty _ g hg,
    entropy_empty _ f hf]
  ring

end Sum

end FiniteProduct
