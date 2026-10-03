/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionGroundSpace
import TNLean.PEPS.RegionPhysicalMap

/-!
# Virtual coordinates of regions with injective site tensors

The product of the site tensor maps embeds the independent virtual
half-edge coordinates into the physical region. The product of their
left inverses is a left inverse of this regional embedding. Applying it
to an actual open-region tensor recovers the virtual bond contractions.

Source: CPGSV21, arXiv:2011.12127, Section IV.C.1, the virtual-pair
argument for injective PEPS, lines 2017–2044; arXiv:1804.04964,
Section 3, the site inverse and contracting-back argument, lines 205–250.
These are finite-graph coordinate identities, not a ground-state
uniqueness assertion.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- Independent virtual configurations at the vertices of a region.
Each internal edge has one label at either endpoint before contraction.
Source: CPGSV21, Section IV.C.1, lines 2017–2044. -/
abbrev RegionVertexVirtualConfig (A : Tensor Γ d) (R : Finset V) :=
  (w : {w : V // w ∈ R}) → LocalVirtualConfig A w.1

/-- The product of the ordinary site tensor maps over a region.
Source: the physical-to-virtual correspondence of CPGSV21,
Section IV.C.1, lines 2017–2044. -/
noncomputable def regionVertexTensorMap (A : Tensor Γ d) (R : Finset V) :
    (RegionVertexVirtualConfig A R → ℂ) →ₗ[ℂ] (RegionPhysicalConfig (d := d) R → ℂ) :=
  regionPhysicalMap R (fun v => LinearMap.toMatrix' (localTensorMap A v))

/-- The product of the chosen site inverses over the region.
Source: the site inverse of arXiv:1804.04964, Section 3, lines 205–250. -/
noncomputable def regionVertexLeftInverse (A : Tensor Γ d) (hA : IsVertexInjective A)
    (R : Finset V) :
    (RegionPhysicalConfig (d := d) R → ℂ) →ₗ[ℂ] (RegionVertexVirtualConfig A R → ℂ) :=
  regionPhysicalMap R (fun v => LinearMap.toMatrix' (localLeftInverse A hA v))

/-- The regional product inverse recovers every independent virtual vector.
Source: tensoring the site inverses in the argument of CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem regionVertexLeftInverse_comp_regionVertexTensorMap
    (A : Tensor Γ d) (hA : IsVertexInjective A) (R : Finset V) :
    regionVertexLeftInverse A hA R ∘ₗ regionVertexTensorMap A R = LinearMap.id := by
  classical
  rw [regionVertexLeftInverse, regionVertexTensorMap, regionPhysicalMap_comp]
  have hcomp (v : V) : localLeftInverse A hA v ∘ₗ localTensorMap A v = LinearMap.id := by
    exact localLeftInverseAt_comp_localTensorMap A (hA v)
  simp only [← LinearMap.toMatrix'_comp, hcomp, LinearMap.toMatrix'_id,
    regionPhysicalMap, regionPhysicalProductMatrix_one, Matrix.mulVecLin_one]

/-- Ordinary site injectivity makes the product regional embedding injective.
Source: the independent site inverses in CPGSV21, Section IV.C.1,
lines 2017–2044. -/
theorem regionVertexTensorMap_injective
    (A : Tensor Γ d) (hA : IsVertexInjective A) (R : Finset V) :
    Function.Injective (regionVertexTensorMap A R) := by
  intro x y hxy
  have h := congrArg (regionVertexLeftInverse A hA R) hxy
  simpa only [← LinearMap.comp_apply, regionVertexLeftInverse_comp_regionVertexTensorMap,
    LinearMap.id_apply] using h

/-- Read every virtual half-edge from a consistent incident-edge assignment.
Source: the virtual pairs in CPGSV21, Section IV.C.1, lines 2017–2044. -/
def regionIncidentVertexConfig (A : Tensor Γ d) (R : Finset V)
    (η : RegionIncidentConfig A R) : RegionVertexVirtualConfig A R :=
  fun w e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩

/-- The virtual region tensor, with every internal bond paired and the
crossing bond labels fixed. Source: CPGSV21, Section IV.C.1,
the virtual entangled-pair argument, lines 2017–2044. -/
noncomputable def regionVirtualBondWeight (A : Tensor Γ d) (R : Finset V)
    (μ : RegionBoundaryConfig A R) : RegionVertexVirtualConfig A R → ℂ :=
  ∑ η : RegionIncidentConfig A R,
    if regionIncidentBoundaryLabel A R η = μ then Pi.single (regionIncidentVertexConfig A R η) 1
    else 0

/-- Arbitrary boundary coefficients for the actual virtual bond tensor.
Source: the regional virtual-pair construction of CPGSV21,
Section IV.C.1, lines 2003–2044. -/
noncomputable def regionVirtualBondMap (A : Tensor Γ d) (R : Finset V) :
    (RegionBoundaryConfig A R → ℂ) →ₗ[ℂ] (RegionVertexVirtualConfig A R → ℂ) :=
  Fintype.linearCombination ℂ (regionVirtualBondWeight A R)

/-- A virtual basis vector is mapped to the product of its site tensors.
Source: the independent site maps in CPGSV21, Section IV.C.1,
lines 2017–2044. -/
theorem regionVertexTensorMap_single (A : Tensor Γ d) (R : Finset V)
    (α : RegionVertexVirtualConfig A R) :
    regionVertexTensorMap A R (Pi.single α 1) =
      fun σ => ∏ w : {w : V // w ∈ R}, A.component w.1 (α w) (σ w) := by
  classical
  funext σ
  simp [regionVertexTensorMap, regionPhysicalMap_apply, Pi.single_apply,
    LinearMap.toMatrix'_apply]

/-- Contracting the virtual bond tensor through the site maps gives the
genuine open-region coefficient. Source: CPGSV21, Section IV.C.1,
lines 2003–2044. -/
theorem regionVertexTensorMap_regionVirtualBondWeight (A : Tensor Γ d) (R : Finset V)
    (μ : RegionBoundaryConfig A R) :
    regionVertexTensorMap A R (regionVirtualBondWeight A R μ) = openRegionWeight A R μ := by
  classical
  rw [regionVirtualBondWeight, map_sum]
  funext σ
  simp only [Finset.sum_apply, openRegionWeight]
  apply Finset.sum_congr rfl
  intro η hη
  split_ifs
  · rw [regionVertexTensorMap_single]
    rfl
  · simp only [map_zero, Pi.zero_apply]

/-- The actual open-region map factors through the virtual bond tensor.
Source: the virtual-pair construction in CPGSV21, Section IV.C.1,
lines 2003–2044. -/
theorem openRegionMap_eq_regionVertexTensorMap_comp_regionVirtualBondMap
    (A : Tensor Γ d) (R : Finset V) :
    openRegionMap A R = regionVertexTensorMap A R ∘ₗ regionVirtualBondMap A R := by
  change Fintype.linearCombination ℂ (openRegionWeight A R) =
    regionVertexTensorMap A R ∘ₗ Fintype.linearCombination ℂ (regionVirtualBondWeight A R)
  have hweight : openRegionWeight A R =
      regionVertexTensorMap A R ∘ regionVirtualBondWeight A R :=
    funext fun μ => (regionVertexTensorMap_regionVirtualBondWeight A R μ).symm
  rw [hweight]
  simp only [← Finsupp.linearCombination_eq_fintype_linearCombination,
    Finsupp.linearCombination_linear_comp, LinearMap.comp_assoc]

/-- The product site inverse recovers the actual virtual bond map.
Source: the inverse step in CPGSV21, Section IV.C.1, lines 2017–2044. -/
theorem regionVertexLeftInverse_comp_openRegionMap
    (A : Tensor Γ d) (hA : IsVertexInjective A) (R : Finset V) :
    regionVertexLeftInverse A hA R ∘ₗ openRegionMap A R = regionVirtualBondMap A R := by
  rw [openRegionMap_eq_regionVertexTensorMap_comp_regionVirtualBondMap,
    ← LinearMap.comp_assoc, regionVertexLeftInverse_comp_regionVertexTensorMap,
    LinearMap.id_comp]

/-- The genuine regional physical space is the image of the virtual bond
space under the product of the site maps. Source: CPGSV21,
Section IV.C.1, lines 2003–2044. -/
theorem regionGroundSpace_eq_map_regionVirtualBondMap_range
    (A : Tensor Γ d) (R : Finset V) :
    regionGroundSpace A R = (regionVirtualBondMap A R).range.map (regionVertexTensorMap A R) := by
  change (openRegionMap A R).range = _
  rw [openRegionMap_eq_regionVertexTensorMap_comp_regionVirtualBondMap, LinearMap.range_comp]

/-- An ordinary injective region has precisely its virtual bond space as
its inverse image in independent virtual coordinates.
Source: the inverse-and-reconstruction argument in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem comap_regionGroundSpace_regionVertexTensorMap
    (A : Tensor Γ d) (hA : IsVertexInjective A) (R : Finset V) :
    (regionGroundSpace A R).comap (regionVertexTensorMap A R) =
      (regionVirtualBondMap A R).range := by
  rw [regionGroundSpace_eq_map_regionVirtualBondMap_range,
    Submodule.comap_map_eq_of_injective (regionVertexTensorMap_injective A hA R)]

end TNLean.PEPS
