/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RangePhysicalParentTransport
import TNLean.PEPS.GInjectivePhysicalMap

/-!
# Full parent-space transport for a fixed G-injective virtual representation

For a fixed virtual representation at each vertex, two G-injective site maps
are related by physical maps which are invertible on their tensor images.
These maps transport every genuine open-region range. For parent regions
covering every vertex, they also transport the entire common ground space and
preserve its dimension, even if the ambient physical dimensions differ.

The finite virtual representations need not be regular; in particular the
result applies to the semi-regular representations of SCP10, Definition 5.1.
It compares tensors for the same virtual representation and the same virtual
bond spaces. The bond-dimension reduction of Section 7 changes those spaces
and is not a consequence of this theorem alone.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 5.1
and Theorems 5.5–5.7, local source lines 1278–1296 and 1360–1588.
-/

open scoped Matrix

namespace TNLean.PEPS

section PhysicalComparison

variable {G W P Q : Type*} [Group G] [Finite G]
variable [AddCommGroup W] [Module ℂ W] [AddCommGroup P] [Module ℂ P]
variable [AddCommGroup Q] [Module ℂ Q]

/-- Two G-injective tensors for the same virtual representation admit a
physical comparison, with no equality of ambient physical dimensions.
Source: consequence of the left inverse in SCP10, Definition 5.1(ii). -/
theorem IsGInjective.exists_physicalMap_comp_eq
    {ρ : Representation ℂ G W} {T : W →ₗ[ℂ] P} {S : W →ₗ[ℂ] Q}
    (hT : IsGInjective ρ T) (hS : IsGInjective ρ S) :
    ∃ F : P →ₗ[ℂ] Q, F ∘ₗ T = S ∧ Set.InjOn F T.range := by
  let := Fintype.ofFinite G
  let : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  obtain ⟨_, L, hL⟩ := (isGInjective_iff_exists_leftInverse ρ T).mp hT
  have hF : (S ∘ₗ L) ∘ₗ T = S := by
    rw [LinearMap.comp_assoc, hL]
    exact LinearMap.ext (apply_averageMap_of_forall_comp_eq hS.invariant)
  refine ⟨S ∘ₗ L, hF, (hT.comp_iff_injOn_range _).mp ?_⟩
  rwa [hF]

end PhysicalComparison

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d e : ℕ}
variable {G : Type*} [Group G] [Finite G]

/-- G-injectivity before and after a physical change implies exact transport
of the common parent space for any vertex-covering family of regions.
The virtual representations may be semi-regular or arbitrary finite-group
representations. Source: consequence of SCP10, Definition 5.1 and Theorem 5.7. -/
theorem map_regionParentGroundSpace_physicalDeform_of_isGInjective
    (A : Tensor Γ d)
    (ρ : (v : V) → Representation ℂ G (LocalVirtualConfig A v → ℂ))
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (hA : ∀ v, IsGInjective (ρ v) (localTensorMap A v))
    (hF : ∀ v, IsGInjective (ρ v) (Matrix.mulVecLin (F v) ∘ₗ localTensorMap A v))
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    (regionParentGroundSpace A R).map (globalPhysicalMap F) =
      regionParentGroundSpace (physicalDeform A F) R :=
  map_regionParentGroundSpace_physicalDeform_of_injOn A F
    (fun v => ((hA v).comp_iff_injOn_range _).mp (hF v)) R hcover

/-- Sitewise G-injectivity for the same virtual representations derives a
physical comparison of the actual tensor families. This hypothesis is local;
no comparison of closed states or parent kernels is assumed.
Source: the site inverses of SCP10, Definition 5.1(ii). -/
theorem exists_physicalDeform_eq_of_isGInjective
    (A : Tensor Γ d) (b : (v : V) → LocalVirtualConfig A v → Fin e → ℂ)
    (ρ : (v : V) → Representation ℂ G (LocalVirtualConfig A v → ℂ))
    (hA : ∀ v, IsGInjective (ρ v) (localTensorMap A v))
    (hB : ∀ v, IsGInjective (ρ v)
      (localTensorMap { bondDim := A.bondDim, component := b } v)) :
    ∃ F : V → Matrix (Fin e) (Fin d) ℂ,
      physicalDeform A F = { bondDim := A.bondDim, component := b } ∧
      ∀ v, Set.InjOn (Matrix.mulVecLin (F v)) (localTensorMap A v).range := by
  classical
  choose F hF hFinj using fun v => (hA v).exists_physicalMap_comp_eq (hB v)
  refine ⟨fun v => LinearMap.toMatrix' (F v), ?_, ?_⟩
  · have hc : (physicalDeform A (fun v => LinearMap.toMatrix' (F v))).component = b := by
      funext v η
      have h := LinearMap.congr_fun (hF v) (Pi.single η 1)
      rw [LinearMap.comp_apply, localTensorMap_apply_single A v η,
        localTensorMap_apply_single (Tensor.mk A.bondDim b) v η] at h
      change LinearMap.toMatrix' (F v) *ᵥ A.component v η = b v η
      rwa [LinearMap.toMatrix'_mulVec]
    exact congrArg (Tensor.mk A.bondDim) hc
  · intro v x hx y hy hxy
    apply hFinj v hx hy
    simpa only [Matrix.mulVecLin_apply, LinearMap.toMatrix'_mulVec] using hxy

/-- G-injective tensor families with the same virtual representations have
physically equivalent local ranges and full parent ground spaces. The map
and its range-injectivity are derived from the local G-injectivity assumptions.
Source: consequence of SCP10, Definition 5.1 and Theorems 5.5–5.7. -/
theorem exists_regionParentGroundSpace_transport_of_isGInjective
    (A : Tensor Γ d) (b : (v : V) → LocalVirtualConfig A v → Fin e → ℂ)
    (ρ : (v : V) → Representation ℂ G (LocalVirtualConfig A v → ℂ))
    (hA : ∀ v, IsGInjective (ρ v) (localTensorMap A v))
    (hB : ∀ v, IsGInjective (ρ v)
      (localTensorMap { bondDim := A.bondDim, component := b } v))
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    ∃ F : V → Matrix (Fin e) (Fin d) ℂ,
      (∀ S : Finset V, (regionGroundSpace A S).map (regionPhysicalMap S F) =
        regionGroundSpace { bondDim := A.bondDim, component := b } S) ∧
      (regionParentGroundSpace A R).map (globalPhysicalMap F) =
        regionParentGroundSpace { bondDim := A.bondDim, component := b } R ∧
      Set.InjOn (globalPhysicalMap F) (regionParentGroundSpace A R) ∧
      Module.finrank ℂ (regionParentGroundSpace { bondDim := A.bondDim, component := b } R) =
        Module.finrank ℂ (regionParentGroundSpace A R) := by
  obtain ⟨F, hF, hinj⟩ := exists_physicalDeform_eq_of_isGInjective A b ρ hA hB
  refine ⟨F, ?_, ?_, globalPhysicalMap_injOn_parent A F hinj R hcover, ?_⟩
  · intro S
    rw [← hF, regionGroundSpace_physicalDeform]
  · rw [← hF]
    exact map_regionParentGroundSpace_physicalDeform_of_injOn A F hinj R hcover
  · rw [← hF]
    exact finrank_regionParentGroundSpace_physicalDeform_of_injOn A F hinj R hcover

/-- The derived physical comparison transports the full kernels of arbitrary
positive parents with the genuine regional ranges. This applies to all fixed
semi-regular virtual representations, without ambient dimension equality.
Source: consequence of SCP10, Definition 5.1 and Theorem 5.7. -/
theorem exists_ker_regionParentHamiltonian_transport_of_isGInjective
    (A : Tensor Γ d) (b : (v : V) → LocalVirtualConfig A v → Fin e → ℂ)
    (ρ : (v : V) → Representation ℂ G (LocalVirtualConfig A v → ℂ))
    (hA : ∀ v, IsGInjective (ρ v) (localTensorMap A v))
    (hB : ∀ v, IsGInjective (ρ v)
      (localTensorMap { bondDim := A.bondDim, component := b } v))
    {ι : Type*} [Fintype ι] (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (K : (i : ι) → Matrix (RegionPhysicalConfig (d := e) (R i))
      (RegionPhysicalConfig (d := e) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction A (R i) (H i))
    (hK : ∀ i, IsRegionParentInteraction
      { bondDim := A.bondDim, component := b } (R i) (K i)) :
    ∃ F : V → Matrix (Fin e) (Fin d) ℂ,
      (Matrix.mulVecLin (regionParentHamiltonian R H)).ker.map (globalPhysicalMap F) =
        (Matrix.mulVecLin (regionParentHamiltonian R K)).ker ∧
      Set.InjOn (globalPhysicalMap F) (Matrix.mulVecLin (regionParentHamiltonian R H)).ker ∧
      Module.finrank ℂ (Matrix.mulVecLin (regionParentHamiltonian R K)).ker =
        Module.finrank ℂ (Matrix.mulVecLin (regionParentHamiltonian R H)).ker := by
  obtain ⟨F, _, hmap, hinj, hdim⟩ :=
    exists_regionParentGroundSpace_transport_of_isGInjective A b ρ hA hB R hcover
  rw [ker_regionParentHamiltonian A R H hH,
    ker_regionParentHamiltonian _ R K hK]
  exact ⟨F, hmap, hinj, hdim⟩

end TNLean.PEPS
