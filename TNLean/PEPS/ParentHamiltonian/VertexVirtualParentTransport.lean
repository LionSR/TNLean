/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.PEPS.ParentHamiltonian.VertexInverseRegionSlice

/-!
# Exact physical and virtual common regional conditions

The product site tensor map sends the genuine common virtual bond conditions
into the genuine common physical regional conditions. With injective site
maps, its image is exactly the physical regional conditions intersected
with the singleton site-image conditions.

Source: the independent site inverses and virtual-pair construction in
CPGSV21, arXiv:2011.12127, Section IV.C.1, lines 2017–2044.
The singleton-image conditions remain explicit; this result does not identify
the common virtual conditions with the global paired-bond space.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] {d : ℕ}
variable {Out : V → Type*}

/-- Split an independent dependent configuration into regional coordinates
and complementary coordinates. -/
def dependentRegionConfigEquiv (R : Finset V) :
    ((w : {w : V // w ∈ Finset.univ}) → Out w.1) ≃
      (((w : {w : V // w ∈ R}) → Out w.1) ×
        ((w : {w : V // w ∈ Finset.univ \ R}) → Out w.1)) where
  toFun η := (fun w => η ⟨w.1, Finset.mem_univ w.1⟩,
    fun w => η ⟨w.1, Finset.mem_univ w.1⟩)
  invFun p := assembleDependentRegionConfig R p.1 p.2
  left_inv η := by
    funext w
    by_cases hw : w.1 ∈ R <;> simp [assembleDependentRegionConfig, hw]
  right_inv p := by
    apply Prod.ext
    · funext w
      simp [assembleDependentRegionConfig, w.2]
    · funext w
      simp [assembleDependentRegionConfig, (Finset.mem_sdiff.mp w.2).2]

variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Literal coefficient formula for the global product site tensor map. -/
theorem globalVertexTensorMap_apply (A : Tensor Γ d)
    (x : RegionVertexVirtualConfig A Finset.univ → ℂ) (σ : V → Fin d) :
    globalVertexTensorMap A x σ =
      ∑ η : RegionVertexVirtualConfig A Finset.univ,
        (∏ v, LinearMap.toMatrix' (localTensorMap A v)
          (σ v) (η ⟨v, Finset.mem_univ v⟩)) * x η := by
  classical
  change regionVertexTensorMap A Finset.univ x (fullRegionConfigEquiv d σ) = _
  rw [regionVertexTensorMap, regionPhysicalMap_apply]
  apply Finset.sum_congr rfl
  intro η _
  congr 1
  exact (Finset.prod_subtype Finset.univ (fun _ => Iff.rfl)
    (fun v => LinearMap.toMatrix' (localTensorMap A v)
      (σ v) (η ⟨v, Finset.mem_univ v⟩))).symm

/-- Each physical regional slice of the product site image is a linear
combination of product-site images of the virtual regional slices.
Source: the independent site contraction in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem regionSliceMap_globalVertexTensorMap (A : Tensor Γ d) (R : Finset V)
    (x : RegionVertexVirtualConfig A Finset.univ → ℂ)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    regionSliceMap R τ (globalVertexTensorMap A x) =
      ∑ β : RegionVertexVirtualConfig A (Finset.univ \ R),
        (∏ w : {w : V // w ∈ Finset.univ \ R},
          LinearMap.toMatrix' (localTensorMap A w.1) (τ w) (β w)) •
          regionVertexTensorMap A R (dependentRegionSlice R β x) := by
  classical
  funext σ
  change globalVertexTensorMap A x (assembleRegionσ R σ τ) = _
  rw [globalVertexTensorMap_apply]
  calc
    _ = ∑ p : RegionVertexVirtualConfig A R ×
          RegionVertexVirtualConfig A (Finset.univ \ R),
        (∏ v, LinearMap.toMatrix' (localTensorMap A v)
          (assembleRegionσ R σ τ v)
          (assembleDependentRegionConfig R p.1 p.2 ⟨v, Finset.mem_univ v⟩)) *
          x (assembleDependentRegionConfig R p.1 p.2) := by
      refine Fintype.sum_equiv (dependentRegionConfigEquiv R) _ _ ?_
      intro η
      have hη : assembleDependentRegionConfig R ((dependentRegionConfigEquiv R) η).1
          ((dependentRegionConfigEquiv R) η).2 = η :=
        (dependentRegionConfigEquiv R).symm_apply_apply η
      rw [hη]
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        regionVertexTensorMap, regionPhysicalMap_apply, Finset.mul_sum]
      apply Finset.sum_congr₂
      intro β _ α _
      have hprod := dependentPhysicalProduct_assembleRegion R
        (fun v => (LinearMap.toMatrix' (localTensorMap A v)).transpose) α β σ τ
      simp only [Matrix.transpose_apply] at hprod
      rw [hprod]
      change _ = _ * (_ * x (assembleDependentRegionConfig R α β))
      ring

variable {ι : Type*}

/-- The product site map sends the common actual virtual regional conditions
into the common actual physical regional conditions. Injectivity is unnecessary.
Source: the virtual-pair contraction in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem globalVertexTensorMap_mem_regionParentGroundSpace
    (A : Tensor Γ d) (R : ι → Finset V)
    {x : RegionVertexVirtualConfig A Finset.univ → ℂ}
    (hx : x ∈ vertexVirtualParentGroundSpace A R) :
    globalVertexTensorMap A x ∈ regionParentGroundSpace A R := by
  rw [mem_vertexVirtualParentGroundSpace_iff] at hx
  rw [mem_regionParentGroundSpace_iff]
  intro i τ
  rw [regionSliceMap_globalVertexTensorMap]
  apply Submodule.sum_smul_mem
  intro β _
  rw [regionGroundSpace_eq_map_regionVirtualBondMap_range]
  exact ⟨dependentRegionSlice (R i) β x, hx i β, rfl⟩

/-- Exact transport of the common virtual conditions: their physical image is
precisely the intersection of the singleton site-image conditions with the
common physical regional conditions. No reconstruction is assumed.
Source: the site-inverse and virtual-pair argument of CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem vertexVirtualParentGroundSpace_map_globalVertexTensorMap
    (A : Tensor Γ d) (hA : IsVertexInjective A) (R : ι → Finset V) :
    (vertexVirtualParentGroundSpace A R).map (globalVertexTensorMap A) =
      vertexImageGroundSpace A ⊓ regionParentGroundSpace A R := by
  apply le_antisymm
  · rintro ψ ⟨x, hx, rfl⟩
    exact ⟨globalVertexTensorMap_mem_vertexImageGroundSpace A hA x,
      globalVertexTensorMap_mem_regionParentGroundSpace A R hx⟩
  · intro ψ hψ
    exact ⟨globalVertexLeftInverse A hA ψ,
      globalVertexLeftInverse_mem_vertexVirtualParentGroundSpace A hA R hψ.2,
      globalVertexTensorMap_leftInverse_eq_self_of_mem A hA hψ.1⟩

end TNLean.PEPS
