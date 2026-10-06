/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.PEPS.ParentHamiltonian.VertexImageGroundSpace

/-!
# Regional slices after the product site inverse

The product site inverse sends a physical regional support condition to
its actual virtual bond support condition. The outside inverse coefficients
merely form a linear combination of the original physical slices.

Source: the independent site inverses and virtual-pair construction in
CPGSV21, arXiv:2011.12127, Section IV.C.1, lines 2017–2044.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] {d : ℕ}
variable {Out : V → Type*}

/-- Assemble a dependent vertex configuration from a region and its complement. -/
def assembleDependentRegionConfig (R : Finset V)
    (α : (w : {w : V // w ∈ R}) → Out w.1)
    (τ : (w : {w : V // w ∈ Finset.univ \ R}) → Out w.1) :
    (w : {w : V // w ∈ Finset.univ}) → Out w.1 :=
  fun w => if h : w.1 ∈ R then α ⟨w.1, h⟩ else τ ⟨w.1, by simp [h]⟩

/-- Apply a product of physical maps with vertex-dependent output spaces. -/
noncomputable def globalDependentPhysicalMap
    (F : (v : V) → Matrix (Out v) (Fin d) ℂ) :
    ((V → Fin d) → ℂ) →ₗ[ℂ]
      (((w : {w : V // w ∈ Finset.univ}) → Out w.1) → ℂ) :=
  regionPhysicalMap Finset.univ F ∘ₗ (fullRegionPhysicalEquiv d).toLinearMap

/-- Extract a regional slice in independent, possibly heterogeneous coordinates. -/
def dependentRegionSlice (R : Finset V)
    (τ : (w : {w : V // w ∈ Finset.univ \ R}) → Out w.1) :
    ((((w : {w : V // w ∈ Finset.univ}) → Out w.1) → ℂ)) →ₗ[ℂ]
      (((w : {w : V // w ∈ R}) → Out w.1) → ℂ) where
  toFun ψ α := ψ (assembleDependentRegionConfig R α τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Literal coefficient formula for the heterogeneous product physical map. -/
theorem globalDependentPhysicalMap_apply
    (F : (v : V) → Matrix (Out v) (Fin d) ℂ)
    (ψ : (V → Fin d) → ℂ)
    (η : (w : {w : V // w ∈ Finset.univ}) → Out w.1) :
    globalDependentPhysicalMap F ψ η =
      ∑ σ : V → Fin d,
        (∏ v, F v (η ⟨v, Finset.mem_univ v⟩) (σ v)) * ψ σ := by
  classical
  change regionPhysicalMap Finset.univ F (fullRegionPhysicalEquiv d ψ) η = _
  rw [regionPhysicalMap_apply]
  refine Fintype.sum_equiv (fullRegionConfigEquiv d).symm _ _ ?_
  intro σ
  change (∏ w : {w : V // w ∈ Finset.univ}, F w.1 (η w) (σ w)) *
    ψ (fun v => σ ⟨v, Finset.mem_univ v⟩) = _
  congr 1
  exact (Finset.prod_subtype Finset.univ (fun _ => Iff.rfl)
    (fun v => F v (η ⟨v, Finset.mem_univ v⟩) (σ ⟨v, Finset.mem_univ v⟩))).symm

/-- The product coefficient splits across a region and its complement.
Source: the finite product of independent site inverses in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem dependentPhysicalProduct_assembleRegion (R : Finset V)
    (F : (v : V) → Matrix (Out v) (Fin d) ℂ)
    (α : (w : {w : V // w ∈ R}) → Out w.1)
    (τ : (w : {w : V // w ∈ Finset.univ \ R}) → Out w.1)
    (σ : RegionPhysicalConfig (d := d) R)
    (β : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    (∏ v, F v ((assembleDependentRegionConfig R α τ) ⟨v, Finset.mem_univ v⟩)
      (assembleRegionσ R σ β v)) =
      (∏ w : {w : V // w ∈ R}, F w.1 (α w) (σ w)) *
        ∏ w : {w : V // w ∈ Finset.univ \ R}, F w.1 (τ w) (β w) := by
  classical
  symm
  calc
    _ = (∏ w : {w : V // w ∈ R},
        F w.1 ((assembleDependentRegionConfig R α τ) ⟨w.1, Finset.mem_univ w.1⟩)
          (assembleRegionσ R σ β w.1)) *
      ∏ w : {w : V // w ∈ Finset.univ \ R},
        F w.1 ((assembleDependentRegionConfig R α τ) ⟨w.1, Finset.mem_univ w.1⟩)
          (assembleRegionσ R σ β w.1) := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro w _
      · simp only [assembleDependentRegionConfig, w.2, dite_true, assembleRegionσ_mem]
      · have hw : w.1 ∉ R := (Finset.mem_sdiff.mp w.2).2
        simp only [assembleDependentRegionConfig, hw, dite_false, assembleRegionσ_notMem]
    _ = _ := by
      rw [← Finset.prod_subtype R (fun _ => Iff.rfl)
          (fun v => F v ((assembleDependentRegionConfig R α τ) ⟨v, Finset.mem_univ v⟩)
            (assembleRegionσ R σ β v)),
        ← Finset.prod_subtype (Finset.univ \ R) (fun _ => Iff.rfl)
          (fun v => F v ((assembleDependentRegionConfig R α τ) ⟨v, Finset.mem_univ v⟩)
            (assembleRegionσ R σ β v)),
        ← Finset.compl_eq_univ_sdiff, Finset.prod_mul_prod_compl]

/-- Each output regional slice is a linear combination of the transformed
original physical slices, including vertex-dependent output spaces.
Source: the independent inverse contraction in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem dependentRegionSlice_globalDependentPhysicalMap (R : Finset V)
    (F : (v : V) → Matrix (Out v) (Fin d) ℂ) (ψ : (V → Fin d) → ℂ)
    (τ : (w : {w : V // w ∈ Finset.univ \ R}) → Out w.1) :
    dependentRegionSlice R τ (globalDependentPhysicalMap F ψ) =
      ∑ β : RegionPhysicalConfig (d := d) (Finset.univ \ R),
        (∏ w : {w : V // w ∈ Finset.univ \ R}, F w.1 (τ w) (β w)) •
          regionPhysicalMap R F (regionSliceMap R β ψ) := by
  classical
  funext α
  change globalDependentPhysicalMap F ψ (assembleDependentRegionConfig R α τ) = _
  rw [globalDependentPhysicalMap_apply]
  calc
    _ = ∑ p : RegionPhysicalConfig (d := d) R ×
          RegionPhysicalConfig (d := d) (Finset.univ \ R),
        (∏ v, F v ((assembleDependentRegionConfig R α τ) ⟨v, Finset.mem_univ v⟩)
          (assembleRegionσ R p.1 p.2 v)) * ψ (assembleRegionσ R p.1 p.2) := by
      refine Fintype.sum_equiv (regionConfigEquiv R) _ _ ?_
      intro ξ
      have hξ : assembleRegionσ R ((regionConfigEquiv R) ξ).1
          ((regionConfigEquiv R) ξ).2 = ξ := (regionConfigEquiv R).symm_apply_apply ξ
      rw [hξ]
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        regionPhysicalMap_apply, Finset.mul_sum]
      apply Finset.sum_congr₂
      intro β _ σ _
      rw [dependentPhysicalProduct_assembleRegion]
      change _ = _ * (_ * ψ (assembleRegionσ R σ β))
      ring

variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The global heterogeneous map of site inverses is the product vertex inverse. -/
theorem globalDependentPhysicalMap_localLeftInverse
    (A : Tensor Γ d) (hA : IsVertexInjective A) :
    globalDependentPhysicalMap (fun v => LinearMap.toMatrix' (localLeftInverse A hA v)) =
      globalVertexLeftInverse A hA := rfl

/-- A physical regional support vector is sent into the actual regional virtual
bond range by the product site inverse. Source: CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem regionVertexLeftInverse_mem_regionVirtualBondMap_range
    (A : Tensor Γ d) (hA : IsVertexInjective A) (R : Finset V)
    {q : RegionPhysicalConfig (d := d) R → ℂ} (hq : q ∈ regionGroundSpace A R) :
    regionVertexLeftInverse A hA R q ∈ (regionVirtualBondMap A R).range := by
  change q ∈ (openRegionMap A R).range at hq
  obtain ⟨μ, rfl⟩ := hq
  exact ⟨μ, by rw [← LinearMap.comp_apply, regionVertexLeftInverse_comp_openRegionMap]⟩

/-- Actual membership of every physical regional slice implies actual virtual
bond-range membership of every regional slice after the global product inverse.
No reconstruction or virtual support condition is assumed.
Source: the site inverse and virtual-pair step in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem dependentRegionSlice_globalVertexLeftInverse_mem
    (A : Tensor Γ d) (hA : IsVertexInjective A) (R : Finset V)
    {ψ : (V → Fin d) → ℂ}
    (hψ : ∀ β : RegionPhysicalConfig (d := d) (Finset.univ \ R),
      regionSliceMap R β ψ ∈ regionGroundSpace A R)
    (τ : RegionVertexVirtualConfig A (Finset.univ \ R)) :
    dependentRegionSlice R τ (globalVertexLeftInverse A hA ψ) ∈
      (regionVirtualBondMap A R).range := by
  rw [← globalDependentPhysicalMap_localLeftInverse,
    dependentRegionSlice_globalDependentPhysicalMap]
  apply Submodule.sum_smul_mem
  intro β _
  exact regionVertexLeftInverse_mem_regionVirtualBondMap_range A hA R (hψ β)

variable {ι : Type*}

/-- Common actual regional virtual bond support conditions.
Source: the independent virtual-pair conditions in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
noncomputable def vertexVirtualParentGroundSpace (A : Tensor Γ d) (R : ι → Finset V) :
    Submodule ℂ (RegionVertexVirtualConfig A Finset.univ → ℂ) :=
  ⨅ i, ⨅ τ : RegionVertexVirtualConfig A (Finset.univ \ R i),
    (regionVirtualBondMap A (R i)).range.comap (dependentRegionSlice (R i) τ)

/-- Membership is exactly the collection of virtual regional slice conditions. -/
theorem mem_vertexVirtualParentGroundSpace_iff (A : Tensor Γ d) (R : ι → Finset V)
    (ξ : RegionVertexVirtualConfig A Finset.univ → ℂ) :
    ξ ∈ vertexVirtualParentGroundSpace A R ↔
      ∀ i, ∀ τ : RegionVertexVirtualConfig A (Finset.univ \ R i),
        dependentRegionSlice (R i) τ ξ ∈ (regionVirtualBondMap A (R i)).range := by
  simp only [vertexVirtualParentGroundSpace, Submodule.mem_iInf, Submodule.mem_comap]

/-- The product site inverse sends every simultaneous physical regional condition
into its actual virtual bond condition. Source: CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem globalVertexLeftInverse_mem_vertexVirtualParentGroundSpace
    (A : Tensor Γ d) (hA : IsVertexInjective A) (R : ι → Finset V)
    {ψ : (V → Fin d) → ℂ} (hψ : ψ ∈ regionParentGroundSpace A R) :
    globalVertexLeftInverse A hA ψ ∈ vertexVirtualParentGroundSpace A R := by
  rw [mem_regionParentGroundSpace_iff] at hψ
  rw [mem_vertexVirtualParentGroundSpace_iff]
  intro i τ
  exact dependentRegionSlice_globalVertexLeftInverse_mem A hA (R i) (hψ i) τ

end TNLean.PEPS
