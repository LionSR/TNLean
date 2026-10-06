/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.PEPS.ParentHamiltonian.RegionPhysicalDeformation

/-!
# Physical transport of the common parent ground space

The product of invertible physical maps on the vertices transports every
regional boundary condition simultaneously. Its restriction therefore gives a
linear equivalence between the common parent ground spaces before and after
physical deformation.

Source: the physical changes of coordinates and concatenation in SCP10,
arXiv:1001.3807, Observation `obs:iso:accessible-virt`, lines 1765–1820,
and the general regional parent construction in arXiv:2011.12127,
Section IV.C.1, lines 2003–2011.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] {d e : ℕ}
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Full configurations and physical configurations on the full vertex region. -/
def fullRegionConfigEquiv (d : ℕ) :
    (V → Fin d) ≃ RegionPhysicalConfig (V := V) (d := d) Finset.univ where
  toFun σ w := σ w.1
  invFun σ v := σ ⟨v, Finset.mem_univ v⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Identify the full physical space with the physical space of the full region. -/
noncomputable def fullRegionPhysicalEquiv (d : ℕ) :
    ((V → Fin d) → ℂ) ≃ₗ[ℂ] (RegionPhysicalConfig (V := V) (d := d) Finset.univ → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (fullRegionConfigEquiv (V := V) d).symm

/-- Apply the product physical map to the full graph. Source: SCP10,
Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
noncomputable def globalPhysicalMap (F : V → Matrix (Fin e) (Fin d) ℂ) :
    ((V → Fin d) → ℂ) →ₗ[ℂ] ((V → Fin e) → ℂ) :=
  (fullRegionPhysicalEquiv e).symm.toLinearMap ∘ₗ
    regionPhysicalMap Finset.univ F ∘ₗ (fullRegionPhysicalEquiv d).toLinearMap

/-- The coefficient formula for the physical map of the full graph. -/
theorem globalPhysicalMap_apply (F : V → Matrix (Fin e) (Fin d) ℂ)
    (ψ : (V → Fin d) → ℂ) (τ : V → Fin e) :
    globalPhysicalMap F ψ τ = ∑ σ : V → Fin d, (∏ v, F v (τ v) (σ v)) * ψ σ := by
  classical
  change regionPhysicalMap Finset.univ F (fullRegionPhysicalEquiv d ψ)
    (fullRegionConfigEquiv e τ) = _
  rw [regionPhysicalMap_apply]
  refine Fintype.sum_equiv (fullRegionConfigEquiv d).symm _ _ ?_
  intro σ
  change (∏ w : {w : V // w ∈ Finset.univ}, F w.1 (τ w.1) (σ w)) *
    ψ (fun v => σ ⟨v, Finset.mem_univ v⟩) = _
  congr 1
  exact (Finset.prod_subtype Finset.univ (fun _ => Iff.rfl)
    (fun v => F v (τ v) (σ ⟨v, Finset.mem_univ v⟩))).symm

/-- The actual closed PEPS vector transforms by the product physical map.
Source: SCP10, concatenation of physical changes of coordinates in Observation
`obs:iso:accessible-virt`, lines 1765–1820. -/
theorem stateCoeff_physicalDeform (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ) :
    stateCoeff (physicalDeform A F) = globalPhysicalMap F (stateCoeff A) := by
  classical
  funext τ
  change (∑ η : VirtualConfig A, ∏ v : V,
    ∑ s : Fin d, F v (τ v) s * A.component v (fun f => η f.1) s) = _
  rw [globalPhysicalMap_apply]
  simp only [stateCoeff, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  simp only [← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun (v : V) (s : Fin d) =>
    F v (τ v) s * A.component v (fun f => η f.1) s)

/-- Product physical isomorphisms give an isomorphism of the full physical space. -/
noncomputable def globalPhysicalEquiv
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) :
    ((V → Fin d) → ℂ) ≃ₗ[ℂ] ((V → Fin e) → ℂ) :=
  (fullRegionPhysicalEquiv d).trans
    ((regionPhysicalEquiv Finset.univ F).trans (fullRegionPhysicalEquiv e).symm)

/-- The product isomorphism has the same action as the product physical map. -/
@[simp]
theorem globalPhysicalEquiv_apply
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) (ψ : (V → Fin d) → ℂ) :
    globalPhysicalEquiv F ψ =
      globalPhysicalMap (fun v => LinearMap.toMatrix' (F v).toLinearMap) ψ := rfl

/-- A physical product coefficient factors across any region and its complement. -/
theorem physicalProduct_assembleRegion (R : Finset V)
    (F : V → Matrix (Fin e) (Fin d) ℂ)
    (σ : RegionPhysicalConfig (d := e) R)
    (τ : RegionPhysicalConfig (d := e) (Finset.univ \ R))
    (α : RegionPhysicalConfig (d := d) R)
    (β : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    (∏ v, F v (assembleRegionσ R σ τ v) (assembleRegionσ R α β v)) =
      (∏ w : {w : V // w ∈ R}, F w.1 (σ w) (α w)) *
        ∏ w : {w : V // w ∈ Finset.univ \ R}, F w.1 (τ w) (β w) := by
  classical
  symm
  calc
    _ = (∏ w : {w : V // w ∈ R},
        F w.1 (assembleRegionσ R σ τ w.1) (assembleRegionσ R α β w.1)) *
      ∏ w : {w : V // w ∈ Finset.univ \ R},
        F w.1 (assembleRegionσ R σ τ w.1) (assembleRegionσ R α β w.1) := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro w _
      · rw [assembleRegionσ_mem, assembleRegionσ_mem]
      · rw [assembleRegionσ_notMem, assembleRegionσ_notMem]
    _ = _ := by
      rw [← Finset.prod_subtype R (fun _ => Iff.rfl)
          (fun v => F v (assembleRegionσ R σ τ v) (assembleRegionσ R α β v)),
        ← Finset.prod_subtype (Finset.univ \ R) (fun _ => Iff.rfl)
          (fun v => F v (assembleRegionσ R σ τ v) (assembleRegionσ R α β v)),
        ← Finset.compl_eq_univ_sdiff, Finset.prod_mul_prod_compl]

/-- After a global physical map, each regional slice is a linear combination
of transformed original slices. Source: SCP10, concatenation of physical maps
in Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem regionSliceMap_globalPhysicalMap (R : Finset V)
    (F : V → Matrix (Fin e) (Fin d) ℂ) (ψ : (V → Fin d) → ℂ)
    (τ : RegionPhysicalConfig (d := e) (Finset.univ \ R)) :
    regionSliceMap R τ (globalPhysicalMap F ψ) =
      ∑ β : RegionPhysicalConfig (d := d) (Finset.univ \ R),
        (∏ w : {w : V // w ∈ Finset.univ \ R}, F w.1 (τ w) (β w)) •
          regionPhysicalMap R F (regionSliceMap R β ψ) := by
  classical
  funext σ
  change globalPhysicalMap F ψ (assembleRegionσ R σ τ) = _
  rw [globalPhysicalMap_apply]
  calc
    _ = ∑ p : RegionPhysicalConfig (d := d) R ×
          RegionPhysicalConfig (d := d) (Finset.univ \ R),
        (∏ v, F v (assembleRegionσ R σ τ v) (assembleRegionσ R p.1 p.2 v)) *
          ψ (assembleRegionσ R p.1 p.2) := by
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
      intro β _ α _
      rw [physicalProduct_assembleRegion]
      change _ = _ * (_ * ψ (assembleRegionσ R α β))
      ring

variable {ι : Type*}

/-- Membership in the common parent ground space is membership of every regional slice. -/
theorem mem_regionParentGroundSpace_iff (A : Tensor Γ d) (R : ι → Finset V)
    (ψ : (V → Fin d) → ℂ) :
    ψ ∈ regionParentGroundSpace A R ↔
      ∀ i, ∀ τ : RegionPhysicalConfig (d := d) (Finset.univ \ R i),
        regionSliceMap (R i) τ ψ ∈ regionGroundSpace A (R i) := by
  simp only [regionParentGroundSpace, Submodule.mem_iInf, Submodule.mem_comap]

/-- Physical product maps transport common regional boundary conditions whenever
they transport the local regional spaces. Source: regional parent construction
in arXiv:2011.12127, Section IV.C.1, lines 2003–2011. -/
theorem globalPhysicalMap_mem_regionParentGroundSpace (A : Tensor Γ d) (B : Tensor Γ e)
    (R : ι → Finset V) (F : V → Matrix (Fin e) (Fin d) ℂ)
    (hF : ∀ i, (regionGroundSpace A (R i)).map (regionPhysicalMap (R i) F) ≤
      regionGroundSpace B (R i)) {ψ : (V → Fin d) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace A R) :
    globalPhysicalMap F ψ ∈ regionParentGroundSpace B R := by
  rw [mem_regionParentGroundSpace_iff] at hψ ⊢
  intro i τ
  rw [regionSliceMap_globalPhysicalMap]
  apply Submodule.sum_smul_mem
  intro β _
  exact hF i ⟨regionSliceMap (R i) β ψ, hψ i β, rfl⟩

/-- Invertible physical maps transport the common parent ground-space conditions
in both directions. Source: concatenation of physical maps in SCP10,
Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem globalPhysicalEquiv_mem_regionParentGroundSpace_iff (A : Tensor Γ d)
    (R : ι → Finset V) (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ))
    (ψ : (V → Fin d) → ℂ) :
    globalPhysicalEquiv F ψ ∈ regionParentGroundSpace
      (physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)) R ↔
      ψ ∈ regionParentGroundSpace A R := by
  let B := physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)
  constructor
  · intro hψ
    have hLocal : ∀ i, (regionGroundSpace B (R i)).map
        (regionPhysicalMap (R i) (fun v => LinearMap.toMatrix' (F v).symm.toLinearMap)) ≤
        regionGroundSpace A (R i) := by
      intro i
      change (regionGroundSpace B (R i)).map (regionPhysicalEquiv (R i) F).symm.toLinearMap ≤ _
      rw [show regionGroundSpace B (R i) =
        (regionGroundSpace A (R i)).map (regionPhysicalEquiv (R i) F).toLinearMap from
          regionGroundSpace_physicalDeform A (R i) _]
      rw [← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id]
    have h := globalPhysicalMap_mem_regionParentGroundSpace B A R
      (fun v => LinearMap.toMatrix' (F v).symm.toLinearMap) hLocal hψ
    change globalPhysicalEquiv (fun v => (F v).symm) (globalPhysicalEquiv F ψ) ∈ _ at h
    convert h using 1
    exact (globalPhysicalEquiv F).symm_apply_apply ψ |>.symm
  · intro hψ
    rw [globalPhysicalEquiv_apply]
    apply globalPhysicalMap_mem_regionParentGroundSpace A _ R _ _ hψ
    intro i
    exact (regionGroundSpace_physicalDeform A (R i) _).ge

/-- The common parent ground space is exactly the image under the full physical product map. -/
theorem map_regionParentGroundSpace_physicalDeform (A : Tensor Γ d) (R : ι → Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) :
    (regionParentGroundSpace A R).map (globalPhysicalEquiv F).toLinearMap =
      regionParentGroundSpace
        (physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)) R := by
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact (globalPhysicalEquiv_mem_regionParentGroundSpace_iff A R F φ).mpr hφ
  · intro hψ
    refine ⟨(globalPhysicalEquiv F).symm ψ, ?_, (globalPhysicalEquiv F).apply_symm_apply ψ⟩
    exact (globalPhysicalEquiv_mem_regionParentGroundSpace_iff A R F _).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using hψ)

/-- Invertible physical deformation identifies the common parent ground spaces. -/
noncomputable def regionParentGroundSpacePhysicalEquiv (A : Tensor Γ d)
    (R : ι → Finset V) (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) :
    regionParentGroundSpace A R ≃ₗ[ℂ] regionParentGroundSpace
      (physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)) R :=
  (globalPhysicalEquiv F).ofSubmodules _ _ (map_regionParentGroundSpace_physicalDeform A R F)

/-- The common ground-space dimension is invariant under invertible physical deformation. -/
theorem finrank_regionParentGroundSpace_physicalDeform (A : Tensor Γ d)
    (R : ι → Finset V) (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) :
    Module.finrank ℂ (regionParentGroundSpace
      (physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)) R) =
      Module.finrank ℂ (regionParentGroundSpace A R) :=
  (regionParentGroundSpacePhysicalEquiv A R F).symm.finrank_eq

variable [Fintype ι]

/-- The kernels of full parent Hamiltonians are transported by the physical product
map when each local interaction is transported by inverse-adjoint congruence.
Source: regional parent construction in arXiv:2011.12127,
Section IV.C.1, lines 2003–2011. -/
theorem map_ker_regionParentHamiltonian_physicalDeform (A : Tensor Γ d)
    (R : ι → Finset V) (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ))
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i)) :
    (Matrix.mulVecLin (regionParentHamiltonian R h)).ker.map (globalPhysicalEquiv F).toLinearMap =
      (Matrix.mulVecLin (regionParentHamiltonian R
        (fun i => deformedRegionInteraction (R i) F (h i)))).ker := by
  rw [ker_regionParentHamiltonian A R h hh,
    ker_regionParentHamiltonian
      (physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)) R
      (fun i => deformedRegionInteraction (R i) F (h i))
      (fun i => (hh i).physicalDeform A (R i) F)]
  exact map_regionParentGroundSpace_physicalDeform A R F

end TNLean.PEPS
