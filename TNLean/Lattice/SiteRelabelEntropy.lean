/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.FiniteProduct
import QICLean.Analysis.EntropyDecomposition
import QICLean.Entropy.SumSitesProduct

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

The product vector `f ⊗ g` on the sites `A ⊕ B` and its entropies are QICLean's
`FiniteProduct.sumSitesProduct`, `FiniteProduct.entropy_sumSitesProduct` and the two
mutual-information statements, in `QICLean/Entropy/SumSitesProduct.lean`.

## Main statements

* `FiniteProduct.entropy_relabelSites`, `FiniteProduct.mutualInformation_relabelSites`.

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


end FiniteProduct
