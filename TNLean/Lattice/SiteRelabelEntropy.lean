/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Entropy.RegionEntropy
import QICLean.Entropy.VonNeumann.EntropyDecomposition
import QICLean.ManyBody.Entropy.SumSitesProduct

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

* `ManyBody.relabelSites`: a vector moved along a bijection of the sites.

The product vector `f ⊗ g` on the sites `A ⊕ B` and its entropies are QICLean's
`ManyBody.sumSitesProduct`, `ManyBody.regionEntropy_sumSitesProduct` and the two
mutual-information statements, in `QICLean/ManyBody/Entropy/SumSitesProduct.lean`.

## Main statements

* `ManyBody.regionEntropy_relabelSites`, `ManyBody.regionMutualInformation_relabelSites`.

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

namespace ManyBody

variable {F : Type*} [Fintype F] [DecidableEq F]

section Relabel

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- A vector on the configurations of `W`, read on `V` through a bijection `σ : V ≃ W`. -/
noncomputable def relabelSites (σ : V ≃ W) (ψ : EuclideanSpace ℂ (W → F)) :
    EuclideanSpace ℂ (V → F) :=
  WithLp.toLp 2 fun c => ψ (c ∘ σ.symm)

/-- Configurations of a region, moved along a bijection of the sites. -/
def regionRelabel (σ : V ≃ W) (S : Finset V) :
    ManyBody.RegionConfig (fun _ : V => F) S ≃ ManyBody.RegionConfig (fun _ : W => F)
        (S.map σ.toEmbedding) :=
  Equiv.arrowCongr (σ.subtypeEquiv fun v => by simp) (Equiv.refl F)

/-- Configurations of the complement of a region, moved along a bijection of the sites. -/
def complRelabel (σ : V ≃ W) (S : Finset V) :
    ManyBody.ComplConfig (fun _ : V => F) S ≃
      ManyBody.ComplConfig (fun _ : W => F) (S.map σ.toEmbedding) :=
  Equiv.arrowCongr (σ.subtypeEquiv fun v => by simp) (Equiv.refl F)

omit [Fintype F] [DecidableEq F] [Fintype V] [Fintype W] in
theorem cutEquiv_symm_comp_relabel (σ : V ≃ W) (S : Finset V)
    (a : ManyBody.RegionConfig (fun _ : V => F) S) (d : ManyBody.ComplConfig (fun _ : V => F) S) :
    (ManyBody.cutEquiv (fun _ : V => F) S).symm (a, d) ∘ σ.symm =
      (ManyBody.cutEquiv (fun _ : W => F) (S.map σ.toEmbedding)).symm
        (regionRelabel σ S a, complRelabel σ S d) := by
  funext w
  by_cases hw : w ∈ S.map σ.toEmbedding
  · have hv : σ.symm w ∈ S := Finset.mem_map_equiv.mp hw
    rw [Function.comp_apply, ManyBody.cutEquiv_symm_apply_mem _ _ hv,
      ManyBody.cutEquiv_symm_apply_mem _ _ hw]
    rfl
  · have hv : σ.symm w ∉ S := fun h => hw (Finset.mem_map_equiv.mpr h)
    rw [Function.comp_apply, ManyBody.cutEquiv_symm_apply_not_mem _ _ hv,
      ManyBody.cutEquiv_symm_apply_not_mem _ _ hw]
    rfl

omit [DecidableEq F] in
/-- The reduced state of a relabelled vector is the reduced state of the original vector
on the image region. -/
theorem regionState_relabelSites (σ : V ≃ W) (ψ : EuclideanSpace ℂ (W → F)) (S : Finset V) :
    ManyBody.regionState (relabelSites σ ψ) S =
      (ManyBody.regionState ψ (S.map σ.toEmbedding)).submatrix
        (regionRelabel σ S) (regionRelabel σ S) := by
  ext a b
  simp only [ManyBody.regionState, ManyBody.regionMatrix_apply, submatrix_apply, vecMulVec_apply,
    Pi.star_apply, relabelSites]
  simp_rw [cutEquiv_symm_comp_relabel]
  exact (complRelabel σ S).sum_comp (fun d => ψ ((ManyBody.cutEquiv (fun _ : W => F)
    (S.map σ.toEmbedding)).symm (regionRelabel σ S a, d)) *
      star (ψ ((ManyBody.cutEquiv (fun _ : W => F) (S.map σ.toEmbedding)).symm
        (regionRelabel σ S b, d))))

/-- **Relabelling sites moves regional entropies.** -/
theorem regionEntropy_relabelSites (σ : V ≃ W) (ψ : EuclideanSpace ℂ (W → F)) (S : Finset V) :
    ManyBody.regionEntropy (relabelSites σ ψ) S =
      ManyBody.regionEntropy ψ (S.map σ.toEmbedding) := by
  unfold ManyBody.regionEntropy
  rw [vonNeumannEntropy_congr (regionState_relabelSites σ ψ S) _
    (((ManyBody.regionState_posSemidef _ ψ).submatrix _).isHermitian)]
  exact vonNeumannEntropy_submatrix_equiv _ _ _

/-- **Relabelling sites moves mutual information.** -/
theorem regionMutualInformation_relabelSites (σ : V ≃ W) (ψ : EuclideanSpace ℂ (W → F))
    (R T : Finset V) :
    ManyBody.regionMutualInformation (relabelSites σ ψ) R T =
      ManyBody.regionMutualInformation ψ (R.map σ.toEmbedding) (T.map σ.toEmbedding) := by
  simp only [ManyBody.regionMutualInformation, regionEntropy_relabelSites, Finset.map_union]

end Relabel


end ManyBody
