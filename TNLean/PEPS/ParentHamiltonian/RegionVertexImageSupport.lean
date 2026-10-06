/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionGroundSpaceNesting
import TNLean.PEPS.ParentHamiltonian.VertexVirtualParentTransport

/-!
# Site-image conditions supplied by regional parent constraints

Every one-site slice of a regional PEPS ground vector belongs to the
image of its site tensor. Hence any collection of parent regions covering
the vertices supplies the site-image conditions needed for virtual
reconstruction. No injectivity or nonzero-bond assumption is required.

Source: CPGSV21, arXiv:2011.12127, the regional contraction and independent
site maps in Section IV.C.1, lines 2003–2044.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- A one-site slice inside a region, with all other regional physical
indices fixed. Source: the independent site maps of CPGSV21,
Section IV.C.1, lines 2017–2044. -/
def regionVertexPhysicalSlice (R : Finset V) (v : {v : V // v ∈ R})
    (τ : RegionPhysicalConfig (d := d) R) :
    (RegionPhysicalConfig (d := d) R → ℂ) →ₗ[ℂ] (Fin d → ℂ) where
  toFun ψ s := ψ (Function.update τ v s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype V] in
/-- A fixed incident assignment separates the selected site's tensor
from the product of all other sites. Source: the product site-map
construction in CPGSV21, Section IV.C.1, lines 2017–2028. -/
theorem regionIncidentWeight_update (A : Tensor Γ d) (R : Finset V)
    (η : RegionIncidentConfig A R) (v : {v : V // v ∈ R})
    (τ : RegionPhysicalConfig (d := d) R) (s : Fin d) :
    regionIncidentWeight A R η (Function.update τ v s) =
      A.component v.1 (regionIncidentVertexConfig A R η v) s *
        ∏ w ∈ Finset.univ.erase v,
          A.component w.1 (regionIncidentVertexConfig A R η w) (τ w) := by
  classical
  unfold regionIncidentWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  rfl

/-- Every one-site slice of an actual regional ground vector lies in its
site tensor image. Source: consequence of the regional contraction in
CPGSV21, Section IV.C.1, lines 2003–2044. -/
theorem regionVertexPhysicalSlice_mem_localTensorMap_range (A : Tensor Γ d)
    (R : Finset V) (v : {v : V // v ∈ R}) (τ : RegionPhysicalConfig (d := d) R)
    {ψ : RegionPhysicalConfig (d := d) R → ℂ} (hψ : ψ ∈ regionGroundSpace A R) :
    regionVertexPhysicalSlice R v τ ψ ∈ (localTensorMap A v.1).range := by
  classical
  obtain ⟨x, rfl⟩ := hψ
  have hs : regionVertexPhysicalSlice R v τ (openRegionMap A R x) =
      ∑ η : RegionIncidentConfig A R,
        x (regionIncidentBoundaryLabel A R η) •
          regionVertexPhysicalSlice R v τ (regionIncidentWeight A R η) := by
    funext s
    change openRegionMap A R x (Function.update τ v s) = _
    rw [openRegionMap_apply, sum_mul_openRegionWeight]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      regionVertexPhysicalSlice, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hs]
  apply Submodule.sum_smul_mem
  intro η _
  let c : ℂ := ∏ w ∈ Finset.univ.erase v,
    A.component w.1 (regionIncidentVertexConfig A R η w) (τ w)
  refine ⟨c • Pi.single (regionIncidentVertexConfig A R η v) 1, ?_⟩
  rw [map_smul, localTensorMap_apply_single]
  funext s
  change c * A.component v.1 (regionIncidentVertexConfig A R η v) s =
    regionIncidentWeight A R η (Function.update τ v s)
  rw [regionIncidentWeight_update, mul_comm]

/-- A parent collection covering every vertex imposes every site-image
condition. Isolated vertices are covered precisely when some region
contains them. Source: the general-graph regional parent construction
in CPGSV21, Section IV.C.1, lines 2003–2044. -/
theorem regionParentGroundSpace_le_vertexImageGroundSpace (A : Tensor Γ d)
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    regionParentGroundSpace A R ≤ vertexImageGroundSpace A := by
  intro ψ hψ
  rw [mem_regionParentGroundSpace_iff] at hψ
  rw [mem_vertexImageGroundSpace_iff]
  intro v τ
  obtain ⟨i, hv⟩ := hcover v
  let α : RegionPhysicalConfig (d := d) (R i) := fun w => τ w.1
  let β : RegionPhysicalConfig (d := d) (Finset.univ \ R i) := fun w => τ w.1
  have hm := regionVertexPhysicalSlice_mem_localTensorMap_range A (R i) ⟨v, hv⟩ α (hψ i β)
  convert hm using 1
  funext s
  change ψ (Function.update τ v s) =
    ψ (assembleRegionσ (R i) (Function.update α ⟨v, hv⟩ s) β)
  congr 1
  funext w
  by_cases hw : w ∈ R i
  · rw [assembleRegionσ_mem (R i) (Function.update α ⟨v, hv⟩ s) β ⟨w, hw⟩]
    by_cases hwv : w = v
    · subst w
      simp [α]
    · have hne : (⟨w, hw⟩ : {w : V // w ∈ R i}) ≠ ⟨v, hv⟩ :=
        fun h => hwv (congrArg Subtype.val h)
      simp [Function.update_of_ne hwv, Function.update_of_ne hne, α]
  · rw [assembleRegionσ_notMem (R i) (Function.update α ⟨v, hv⟩ s) β
      ⟨w, by simp [hw]⟩]
    have hwv : w ≠ v := fun h => hw (h ▸ hv)
    simp [Function.update_of_ne hwv, β]

/-- For a collection covering every vertex, the actual physical common
parent space is exactly the product-site image of its virtual regional
conditions. Source: consequence of the site-inverse parent argument
in CPGSV21, Section IV.C.1, lines 2003–2044. -/
theorem vertexVirtualParentGroundSpace_map_globalVertexTensorMap_of_cover
    (A : Tensor Γ d) (hA : IsVertexInjective A) {ι : Type*}
    (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    (vertexVirtualParentGroundSpace A R).map (globalVertexTensorMap A) =
      regionParentGroundSpace A R := by
  rw [vertexVirtualParentGroundSpace_map_globalVertexTensorMap A hA R]
  exact inf_of_le_right (regionParentGroundSpace_le_vertexImageGroundSpace A R hcover)

/-- Every positive exact-kernel parent family on a vertex-covering collection
has the image of the actual common virtual regional space as its kernel.
Source: finite-graph consequence of the regional construction and site
inverse argument in CPGSV21, Section IV.C.1, lines 2003–2044. -/
theorem ker_regionParentHamiltonian_eq_virtual_image_of_cover
    (A : Tensor Γ d) (hA : IsVertexInjective A) {ι : Type*} [Fintype ι]
    (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction A (R i) (H i)) :
    (Matrix.mulVecLin (regionParentHamiltonian R H)).ker =
      (vertexVirtualParentGroundSpace A R).map (globalVertexTensorMap A) := by
  rw [ker_regionParentHamiltonian A R H hH,
    vertexVirtualParentGroundSpace_map_globalVertexTensorMap_of_cover A hA R hcover]

end TNLean.PEPS
