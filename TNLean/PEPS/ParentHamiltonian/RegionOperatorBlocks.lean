/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionPhysicalGroundSpaceTransport

/-!
# Regional blocks of global physical operators

Fixing the input and output configurations outside a region gives a matrix
between the physical spaces inside the region. Every output slice of a global
matrix-vector product is the sum of these blocks applied to the input slices.
Consequently, inclusions between the genuine regional PEPS ranges imply an
inclusion between their common parent ground spaces.

This is a general linear-algebra statement for regional boundary conditions;
it does not assume a global parent-kernel equality. The regional ground-space
construction is that of arXiv:2011.12127, Section IV.C.1, lines 2003–2011.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] {d e : ℕ}

/-- The block of a global operator obtained by fixing both configurations outside
a region. Its row and column indices are the configurations inside the region. -/
def regionOperatorBlock (R : Finset V) (M : Matrix (V → Fin e) (V → Fin d) ℂ)
    (τ : RegionPhysicalConfig (d := e) (Finset.univ \ R))
    (σ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    Matrix (RegionPhysicalConfig (d := e) R) (RegionPhysicalConfig (d := d) R) ℂ :=
  fun y x => M (assembleRegionσ R y τ) (assembleRegionσ R x σ)

/-- A slice of a global matrix-vector product is the sum of the regional blocks
applied to the corresponding input slices. -/
theorem regionSliceMap_mulVec (R : Finset V)
    (M : Matrix (V → Fin e) (V → Fin d) ℂ) (ψ : (V → Fin d) → ℂ)
    (τ : RegionPhysicalConfig (d := e) (Finset.univ \ R)) :
    regionSliceMap R τ (M *ᵥ ψ) =
      ∑ σ : RegionPhysicalConfig (d := d) (Finset.univ \ R),
        regionOperatorBlock R M τ σ *ᵥ regionSliceMap R σ ψ := by
  classical
  funext y
  change (∑ ξ : V → Fin d, M (assembleRegionσ R y τ) ξ * ψ ξ) = _
  calc
    _ = ∑ p : RegionPhysicalConfig (d := d) R ×
          RegionPhysicalConfig (d := d) (Finset.univ \ R),
        M (assembleRegionσ R y τ) (assembleRegionσ R p.1 p.2) *
          ψ (assembleRegionσ R p.1 p.2) := by
      refine Fintype.sum_equiv (regionConfigEquiv R) _ _ ?_
      intro ξ
      have hξ : assembleRegionσ R ((regionConfigEquiv R) ξ).1
          ((regionConfigEquiv R) ξ).2 = ξ := (regionConfigEquiv R).symm_apply_apply ξ
      rw [hξ]
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, regionOperatorBlock,
        regionSliceMap, LinearMap.coe_mk, AddHom.coe_mk]

/-- Taking adjoints exchanges the fixed input and output configurations of a block. -/
@[simp]
theorem regionOperatorBlock_conjTranspose (R : Finset V)
    (M : Matrix (V → Fin e) (V → Fin d) ℂ)
    (σ : RegionPhysicalConfig (d := d) (Finset.univ \ R))
    (τ : RegionPhysicalConfig (d := e) (Finset.univ \ R)) :
    regionOperatorBlock R M.conjTranspose σ τ =
      (regionOperatorBlock R M τ σ).conjTranspose := rfl

variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {ι : Type*}

/-- A global matrix preserves common parent conditions if every regional block
sends the corresponding source PEPS range into the target PEPS range.
The hypothesis concerns actual regional ranges, with both outside configurations
arbitrary, rather than a prescribed global kernel. -/
theorem mulVec_mem_regionParentGroundSpace_of_blocks (A : Tensor Γ d) (B : Tensor Γ e)
    (R : ι → Finset V) (M : Matrix (V → Fin e) (V → Fin d) ℂ)
    (hM : ∀ i, ∀ τ : RegionPhysicalConfig (d := e) (Finset.univ \ R i),
      ∀ σ : RegionPhysicalConfig (d := d) (Finset.univ \ R i),
        (regionGroundSpace A (R i)).map
          (Matrix.mulVecLin (regionOperatorBlock (R i) M τ σ)) ≤
            regionGroundSpace B (R i))
    {ψ : (V → Fin d) → ℂ} (hψ : ψ ∈ regionParentGroundSpace A R) :
    M *ᵥ ψ ∈ regionParentGroundSpace B R := by
  classical
  rw [mem_regionParentGroundSpace_iff] at hψ ⊢
  intro i τ
  rw [regionSliceMap_mulVec]
  apply Submodule.sum_mem
  intro σ _
  exact hM i τ σ ⟨regionSliceMap (R i) σ ψ, hψ i σ, rfl⟩

/-- Regional block range inclusions lift to the image inclusion of common parent
ground spaces under the global matrix. -/
theorem map_regionParentGroundSpace_le_of_blocks (A : Tensor Γ d) (B : Tensor Γ e)
    (R : ι → Finset V) (M : Matrix (V → Fin e) (V → Fin d) ℂ)
    (hM : ∀ i, ∀ τ : RegionPhysicalConfig (d := e) (Finset.univ \ R i),
      ∀ σ : RegionPhysicalConfig (d := d) (Finset.univ \ R i),
        (regionGroundSpace A (R i)).map
          (Matrix.mulVecLin (regionOperatorBlock (R i) M τ σ)) ≤
            regionGroundSpace B (R i)) :
    (regionParentGroundSpace A R).map (Matrix.mulVecLin M) ≤
      regionParentGroundSpace B R := by
  rintro _ ⟨ψ, hψ, rfl⟩
  exact mulVec_mem_regionParentGroundSpace_of_blocks A B R M hM hψ

end TNLean.PEPS
