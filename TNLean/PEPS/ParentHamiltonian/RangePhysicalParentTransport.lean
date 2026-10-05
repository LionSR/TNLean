/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionVertexImageSupport

/-!
# Parent ground spaces under physical maps injective on the site images

A physical map need only be invertible on the image of each site tensor to
transport the whole parent ground space. The ambient physical dimensions may
differ. A collection of parent regions covering every vertex supplies the
site-image conditions, so local inverses reconstruct every ground vector.
The resulting equivalence concerns the genuine open-region ranges and common
parent kernels, rather than a selected closed state.

Source: consequence of the physical changes of coordinates and site inverses
in SCP10, arXiv:1001.3807, Definition 5.1 and Theorems 5.5–5.7,
lines 1278–1296 and 1360–1588. No change of virtual representation is asserted.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d e : ℕ}

/-- A product physical map fixing each site image fixes every vector satisfying
all single-site image conditions. Source: SCP10, Definition 5.1(ii). -/
theorem globalPhysicalMap_eq_self_of_fixes_site_ranges (A : Tensor Γ d)
    (P : V → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ v, ∀ x ∈ (localTensorMap A v).range, P v *ᵥ x = x)
    {ψ : (V → Fin d) → ℂ} (hψ : ψ ∈ vertexImageGroundSpace A) :
    globalPhysicalMap P ψ = ψ := by
  apply globalPhysicalMap_fixed_of_oneVertex_fixed
  intro v
  funext τ
  rw [globalPhysicalMap_oneVertex_apply]
  have h := congrFun (hP v _ ((mem_vertexImageGroundSpace_iff A ψ).mp hψ v τ)) (τ v)
  simpa only [Matrix.mulVec, dotProduct, vertexPhysicalSlice, LinearMap.coe_mk,
    AddHom.coe_mk, Function.update_eq_self] using h

/-- A sitewise inverse on the tensor ranges reverses physical deformation
as an identity of actual tensors. Source: SCP10, Definition 5.1(ii). -/
theorem physicalDeform_physicalDeform_eq_of_leftInverse (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ) (L : V → Matrix (Fin d) (Fin e) ℂ)
    (hLF : ∀ v, ∀ x ∈ (localTensorMap A v).range, L v *ᵥ (F v *ᵥ x) = x) :
    physicalDeform (physicalDeform A F) L = A := by
  have hcomp : (physicalDeform (physicalDeform A F) L).component = A.component := by
    funext v η s
    have h := congrFun (hLF v (A.component v η)
      ⟨Pi.single η 1, localTensorMap_apply_single A v η⟩) s
    exact h
  cases A with
  | mk D a => exact congrArg (Tensor.mk D) hcomp

/-- Local inverses on the tensor images reconstruct every parent ground vector
when the parent regions cover the vertices. Source: SCP10, Definition 5.1(ii)
and the parent construction of Theorem 5.7. -/
theorem globalPhysicalMap_leftInverse_of_mem_parent (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ) (L : V → Matrix (Fin d) (Fin e) ℂ)
    (hLF : ∀ v, ∀ x ∈ (localTensorMap A v).range, L v *ᵥ (F v *ᵥ x) = x)
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i)
    {ψ : (V → Fin d) → ℂ} (hψ : ψ ∈ regionParentGroundSpace A R) :
    globalPhysicalMap L (globalPhysicalMap F ψ) = ψ := by
  rw [← LinearMap.comp_apply, globalPhysicalMap_comp]
  apply globalPhysicalMap_eq_self_of_fixes_site_ranges A _ _
    (regionParentGroundSpace_le_vertexImageGroundSpace A R hcover hψ)
  intro v x hx
  rw [← Matrix.mulVec_mulVec]
  exact hLF v x hx

/-- Every physical product map sends parent ground vectors to ground vectors
of the physically deformed tensor, without an injectivity hypothesis.
Source: the regional contraction of SCP10, Theorem 5.7. -/
theorem globalPhysicalMap_mem_parent_physicalDeform (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ) {ι : Type*} (R : ι → Finset V)
    {ψ : (V → Fin d) → ℂ} (hψ : ψ ∈ regionParentGroundSpace A R) :
    globalPhysicalMap F ψ ∈ regionParentGroundSpace (physicalDeform A F) R := by
  apply globalPhysicalMap_mem_regionParentGroundSpace A _ R F _ hψ
  intro i
  exact (regionGroundSpace_physicalDeform A (R i) F).ge

/-- The opposite composition fixes the deformed site images. No inverse is
required on the unused physical subspaces. Source: SCP10, Definition 5.1(ii). -/
theorem physicalDeform_rightInverse_on_site_ranges (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ) (L : V → Matrix (Fin d) (Fin e) ℂ)
    (hLF : ∀ v, ∀ x ∈ (localTensorMap A v).range, L v *ᵥ (F v *ᵥ x) = x) :
    ∀ v, ∀ y ∈ (localTensorMap (physicalDeform A F) v).range,
      F v *ᵥ (L v *ᵥ y) = y := by
  intro v y hy
  obtain ⟨x, rfl⟩ := hy
  have hmap : localTensorMap (physicalDeform A F) v x =
      F v *ᵥ localTensorMap A v x := by
    change (∑ η, x η • (F v *ᵥ A.component v η)) =
      Matrix.mulVecLin (F v) (∑ η, x η • A.component v η)
    simp only [map_sum, map_smul, Matrix.mulVecLin_apply]
  rw [hmap, hLF v _ ⟨x, rfl⟩]

/-- Physical maps invertible on each tensor image transport the entire common
parent space, provided the parent regions cover all vertices.
Source: consequence of SCP10, Definition 5.1(ii) and Theorem 5.7. -/
theorem map_regionParentGroundSpace_physicalDeform_of_leftInverse (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ) (L : V → Matrix (Fin d) (Fin e) ℂ)
    (hLF : ∀ v, ∀ x ∈ (localTensorMap A v).range, L v *ᵥ (F v *ᵥ x) = x)
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    (regionParentGroundSpace A R).map (globalPhysicalMap F) =
      regionParentGroundSpace (physicalDeform A F) R := by
  have hA := physicalDeform_physicalDeform_eq_of_leftInverse A F L hLF
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact globalPhysicalMap_mem_parent_physicalDeform A F R hφ
  · intro hψ
    refine ⟨globalPhysicalMap L ψ, ?_, ?_⟩
    · change globalPhysicalMap L ψ ∈ regionParentGroundSpace A R
      rw [← hA]
      exact globalPhysicalMap_mem_parent_physicalDeform (physicalDeform A F) L R hψ
    · exact globalPhysicalMap_leftInverse_of_mem_parent (physicalDeform A F) L F
        (physicalDeform_rightInverse_on_site_ranges A F L hLF) R hcover hψ

/-- A physical map injective on a site's range admits a linear inverse on
that range; no ambient injectivity or equality of dimensions is needed. -/
theorem exists_siteRange_leftInverse (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (hF : ∀ v, Set.InjOn (Matrix.mulVecLin (F v)) (localTensorMap A v).range) :
    ∃ L : V → Matrix (Fin d) (Fin e) ℂ,
      ∀ v, ∀ x ∈ (localTensorMap A v).range, L v *ᵥ (F v *ᵥ x) = x := by
  classical
  have h (v : V) : Function.Injective
      (Matrix.mulVecLin (F v) ∘ₗ (localTensorMap A v).range.subtype) := by
    intro x y hxy
    exact Subtype.ext (hF v x.2 y.2 hxy)
  choose L hL using fun v => LinearMap.exists_leftInverse_of_injective _
    (LinearMap.ker_eq_bot.mpr (h v))
  refine ⟨fun v => LinearMap.toMatrix' ((localTensorMap A v).range.subtype ∘ₗ L v), ?_⟩
  intro v x hx
  have h := congrArg Subtype.val (LinearMap.congr_fun (hL v) ⟨x, hx⟩)
  simpa only [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.id_apply, Matrix.mulVecLin_apply] using h

/-- Injectivity on the site tensor ranges suffices for exact transport of
all parent ground vectors. Source: consequence of SCP10, Definition 5.1
and Theorem 5.7. -/
theorem map_regionParentGroundSpace_physicalDeform_of_injOn (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (hF : ∀ v, Set.InjOn (Matrix.mulVecLin (F v)) (localTensorMap A v).range)
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    (regionParentGroundSpace A R).map (globalPhysicalMap F) =
      regionParentGroundSpace (physicalDeform A F) R := by
  obtain ⟨L, hL⟩ := exists_siteRange_leftInverse A F hF
  exact map_regionParentGroundSpace_physicalDeform_of_leftInverse A F L hL R hcover

/-- The same local inverse reverses the physical change on every genuine
open-region vector, with arbitrary virtual boundary conditions. -/
theorem regionPhysicalMap_leftInverse_on_regionGroundSpace (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ) (L : V → Matrix (Fin d) (Fin e) ℂ)
    (hLF : ∀ v, ∀ x ∈ (localTensorMap A v).range, L v *ᵥ (F v *ᵥ x) = x)
    (R : Finset V) {ψ : RegionPhysicalConfig (d := d) R → ℂ}
    (hψ : ψ ∈ regionGroundSpace A R) :
    regionPhysicalMap R L (regionPhysicalMap R F ψ) = ψ := by
  obtain ⟨x, rfl⟩ := hψ
  change regionPhysicalMap R L ((regionPhysicalMap R F ∘ₗ openRegionMap A R) x) = _
  rw [← openRegionMap_physicalDeform]
  change (regionPhysicalMap R L ∘ₗ openRegionMap (physicalDeform A F) R) x = _
  rw [← openRegionMap_physicalDeform]
  have hc : (physicalDeform (physicalDeform A F) L).component = A.component := by
    funext v η s
    exact congrFun (hLF v (A.component v η)
      ⟨Pi.single η 1, localTensorMap_apply_single A v η⟩) s
  exact congrArg (fun c => openRegionMap (Tensor.mk A.bondDim c) R x) hc

/-- Site-image injectivity implies injectivity on each full open-region
range, including all virtual boundary conditions. -/
theorem regionPhysicalMap_injOn_regionGroundSpace (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (hF : ∀ v, Set.InjOn (Matrix.mulVecLin (F v)) (localTensorMap A v).range)
    (R : Finset V) :
    Set.InjOn (regionPhysicalMap R F) (regionGroundSpace A R) := by
  obtain ⟨L, hL⟩ := exists_siteRange_leftInverse A F hF
  intro ψ hψ φ hφ hEq
  have h := congrArg (regionPhysicalMap R L) hEq
  rwa [regionPhysicalMap_leftInverse_on_regionGroundSpace A F L hL R hψ,
    regionPhysicalMap_leftInverse_on_regionGroundSpace A F L hL R hφ] at h

/-- The product physical map is injective on the parent ground space when it
is injective on every site image and the regions cover the vertices. -/
theorem globalPhysicalMap_injOn_parent (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (hF : ∀ v, Set.InjOn (Matrix.mulVecLin (F v)) (localTensorMap A v).range)
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    Set.InjOn (globalPhysicalMap F) (regionParentGroundSpace A R) := by
  obtain ⟨L, hL⟩ := exists_siteRange_leftInverse A F hF
  intro ψ hψ φ hφ hEq
  have h := congrArg (globalPhysicalMap L) hEq
  rwa [globalPhysicalMap_leftInverse_of_mem_parent A F L hL R hcover hψ,
    globalPhysicalMap_leftInverse_of_mem_parent A F L hL R hcover hφ] at h

/-- Restrict the physical product map to obtain an equivalence of the entire
parent ground spaces, even for different ambient physical dimensions. -/
noncomputable def regionParentGroundSpaceRangeEquiv (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (hF : ∀ v, Set.InjOn (Matrix.mulVecLin (F v)) (localTensorMap A v).range)
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    regionParentGroundSpace A R ≃ₗ[ℂ] regionParentGroundSpace (physicalDeform A F) R :=
  LinearEquiv.ofBijective
    (((globalPhysicalMap F) ∘ₗ (regionParentGroundSpace A R).subtype).codRestrict _
      (fun ψ => globalPhysicalMap_mem_parent_physicalDeform A F R ψ.2))
    ⟨fun ψ φ h => Subtype.ext (globalPhysicalMap_injOn_parent A F hF R hcover
        ψ.2 φ.2 (congrArg Subtype.val h)), by
      intro ψ
      have hψ := (map_regionParentGroundSpace_physicalDeform_of_injOn A F hF R hcover).ge ψ.2
      obtain ⟨φ, hφ, hEq⟩ := hψ
      exact ⟨⟨φ, hφ⟩, Subtype.ext hEq⟩⟩

/-- Site-image-injective physical maps preserve the full ground-space dimension
for vertex-covering parent regions. -/
theorem finrank_regionParentGroundSpace_physicalDeform_of_injOn (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (hF : ∀ v, Set.InjOn (Matrix.mulVecLin (F v)) (localTensorMap A v).range)
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    Module.finrank ℂ (regionParentGroundSpace (physicalDeform A F) R) =
      Module.finrank ℂ (regionParentGroundSpace A R) :=
  (regionParentGroundSpaceRangeEquiv A F hF R hcover).symm.finrank_eq

/-- Any positive parent interactions with the genuine regional kernels before
and after deformation have full kernels related by the physical product map.
The interactions need not be obtained from one another by conjugation.
Source: the exact local-kernel parent construction of SCP10, Theorem 5.7. -/
theorem map_ker_regionParentHamiltonian_physicalDeform_of_injOn (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (hF : ∀ v, Set.InjOn (Matrix.mulVecLin (F v)) (localTensorMap A v).range)
    {ι : Type*} [Fintype ι] (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (K : (i : ι) → Matrix (RegionPhysicalConfig (d := e) (R i))
      (RegionPhysicalConfig (d := e) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction A (R i) (H i))
    (hK : ∀ i, IsRegionParentInteraction (physicalDeform A F) (R i) (K i)) :
    (Matrix.mulVecLin (regionParentHamiltonian R H)).ker.map (globalPhysicalMap F) =
      (Matrix.mulVecLin (regionParentHamiltonian R K)).ker := by
  rw [ker_regionParentHamiltonian A R H hH,
    ker_regionParentHamiltonian (physicalDeform A F) R K hK]
  exact map_regionParentGroundSpace_physicalDeform_of_injOn A F hF R hcover

end TNLean.PEPS
