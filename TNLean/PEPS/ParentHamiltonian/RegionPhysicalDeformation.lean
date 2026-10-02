/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionParentHamiltonian
import TNLean.PEPS.RegionPhysicalMap
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Regional ground spaces under physical changes of coordinates

A linear map on each physical leg commutes with the contraction of the internal
bonds. Consequently the genuine regional ground space transforms by the product
of those physical maps. Invertible physical maps give a linear equivalence of the
regional spaces and preserve their dimensions.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Observation
`obs:iso:accessible-virt` and its concatenation argument,
`Papers/1001.3807/paper_v3.tex`, lines 1765–1820. The covariance statements below
hold for arbitrary finite graphs and do not require group injectivity.
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d e : ℕ}

/-- Apply a physical linear map at every vertex, keeping every virtual bond.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
noncomputable def physicalDeform (A : Tensor Γ d)
    (F : V → Matrix (Fin e) (Fin d) ℂ) : Tensor Γ e where
  bondDim := A.bondDim
  component v η t := ∑ s, F v t s * A.component v η s

/-- Physical deformation of an open-region tensor is the regional product map.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem openRegionWeight_physicalDeform (A : Tensor Γ d) (R : Finset V)
    (F : V → Matrix (Fin e) (Fin d) ℂ) (μ : RegionBoundaryConfig A R) :
    openRegionWeight (physicalDeform A F) R μ =
      regionPhysicalMap R F (openRegionWeight A R μ) := by
  funext τ
  rw [regionPhysicalMap_openRegionWeight]
  rfl

/-- The genuine open-region maps commute with physical deformation.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem openRegionMap_physicalDeform (A : Tensor Γ d) (R : Finset V)
    (F : V → Matrix (Fin e) (Fin d) ℂ) :
    openRegionMap (physicalDeform A F) R =
      regionPhysicalMap R F ∘ₗ openRegionMap A R := by
  classical
  apply LinearMap.ext
  intro x
  change (∑ μ : RegionBoundaryConfig A R, x μ • openRegionWeight (physicalDeform A F) R μ) =
    regionPhysicalMap R F (∑ μ : RegionBoundaryConfig A R, x μ • openRegionWeight A R μ)
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun μ _ => congrArg (fun ψ => x μ • ψ)
    (openRegionWeight_physicalDeform A R F μ)

/-- The regional ground space is transported by the product physical map.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem regionGroundSpace_physicalDeform (A : Tensor Γ d) (R : Finset V)
    (F : V → Matrix (Fin e) (Fin d) ℂ) :
    regionGroundSpace (physicalDeform A F) R =
      (regionGroundSpace A R).map (regionPhysicalMap R F) := by
  change (openRegionMap (physicalDeform A F) R).range =
    (openRegionMap A R).range.map (regionPhysicalMap R F)
  have h := congrArg LinearMap.range (openRegionMap_physicalDeform A R F)
  exact h.trans (LinearMap.range_comp _ _)

/-- The product of invertible physical maps is an invertible regional map.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
noncomputable def regionPhysicalEquiv (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) :
    (RegionPhysicalConfig (d := d) R → ℂ) ≃ₗ[ℂ]
      (RegionPhysicalConfig (d := e) R → ℂ) :=
  LinearEquiv.ofLinearMap
    (regionPhysicalMap R (fun v => LinearMap.toMatrix' (F v).toLinearMap))
    (regionPhysicalMap R (fun v => LinearMap.toMatrix' (F v).symm.toLinearMap))
    (by
      rw [regionPhysicalMap_comp]
      simp only [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm,
        LinearMap.toMatrix'_id, regionPhysicalMap, regionPhysicalProductMatrix_one,
        Matrix.mulVecLin_one])
    (by
      rw [regionPhysicalMap_comp]
      simp only [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp,
        LinearMap.toMatrix'_id, regionPhysicalMap, regionPhysicalProductMatrix_one,
        Matrix.mulVecLin_one])

/-- Invertible physical deformation identifies the genuine regional spaces.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
noncomputable def regionGroundSpacePhysicalEquiv (A : Tensor Γ d) (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) :
    regionGroundSpace A R ≃ₗ[ℂ]
      regionGroundSpace (physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)) R :=
  (regionPhysicalEquiv R F).ofSubmodules _ _
    (regionGroundSpace_physicalDeform A R _).symm

/-- The regional-space equivalence is the product physical map on its vectors.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
@[simp]
theorem regionGroundSpacePhysicalEquiv_apply (A : Tensor Γ d) (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) (ψ : regionGroundSpace A R) :
    (regionGroundSpacePhysicalEquiv A R F ψ : RegionPhysicalConfig (d := e) R → ℂ) =
      regionPhysicalEquiv R F ψ := rfl

/-- An invertible physical deformation preserves precisely regional-space membership.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem regionPhysicalEquiv_mem_regionGroundSpace_iff (A : Tensor Γ d) (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) (ψ : RegionPhysicalConfig (d := d) R → ℂ) :
    regionPhysicalEquiv R F ψ ∈
      regionGroundSpace (physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)) R ↔
      ψ ∈ regionGroundSpace A R := by
  rw [regionGroundSpace_physicalDeform]
  change regionPhysicalEquiv R F ψ ∈ (regionGroundSpace A R).map
    (regionPhysicalEquiv R F).toLinearMap ↔ _
  constructor
  · rintro ⟨φ, hφ, hEq⟩
    exact (regionPhysicalEquiv R F).injective hEq ▸ hφ
  · intro hψ
    exact ⟨ψ, hψ, rfl⟩

/-- Invertible physical deformation preserves the virtual kernel of each open-region map.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem ker_openRegionMap_physicalDeform (A : Tensor Γ d) (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) :
    (openRegionMap (physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)) R).ker =
      (openRegionMap A R).ker := by
  have h := congrArg LinearMap.ker (openRegionMap_physicalDeform A R
    (fun v => LinearMap.toMatrix' (F v).toLinearMap))
  change _ = ((regionPhysicalEquiv R F).toLinearMap ∘ₗ openRegionMap A R).ker at h
  exact h.trans (LinearMap.ker_comp_of_ker_eq_bot _ (regionPhysicalEquiv R F).ker)

/-- Invertible physical deformation preserves the dimension of every regional space.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem finrank_regionGroundSpace_physicalDeform (A : Tensor Γ d) (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) :
    Module.finrank ℂ
      (regionGroundSpace (physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)) R) =
      Module.finrank ℂ (regionGroundSpace A R) :=
  (regionGroundSpacePhysicalEquiv A R F).symm.finrank_eq

/-- Transport a local interaction by the inverse physical change of coordinates.
Source: inverse-adjoint congruence of the parent interactions in
arXiv:2011.12127, Section IV.C.1, lines 2003–2011. -/
noncomputable def deformedRegionInteraction (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ))
    (h : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ) :
    Matrix (RegionPhysicalConfig (d := e) R) (RegionPhysicalConfig (d := e) R) ℂ :=
  let Q := LinearMap.toMatrix' (regionPhysicalEquiv R F).symm.toLinearMap
  Q.conjTranspose * h * Q

omit [Fintype V] in
/-- Positive interactions remain positive under arbitrary invertible physical deformation.
Source: inverse-adjoint congruence of the parent interactions in
arXiv:2011.12127, Section IV.C.1, lines 2003–2011. -/
theorem deformedRegionInteraction_posSemidef (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ))
    {h : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ}
    (hh : h.PosSemidef) : (deformedRegionInteraction R F h).PosSemidef :=
  hh.conjTranspose_mul_mul_same _

omit [Fintype V] in
/-- The transported interaction annihilates exactly the transformed vectors from its kernel.
Source: inverse-adjoint congruence of the parent interactions in
arXiv:2011.12127, Section IV.C.1, lines 2003–2011. -/
theorem deformedRegionInteraction_mulVec_eq_zero_iff (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ))
    (h : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (ψ : RegionPhysicalConfig (d := e) R → ℂ) :
    deformedRegionInteraction R F h *ᵥ ψ = 0 ↔
      h *ᵥ (regionPhysicalEquiv R F).symm ψ = 0 := by
  classical
  let E := regionPhysicalEquiv R F
  let Q := LinearMap.toMatrix' E.symm.toLinearMap
  let L := LinearMap.toMatrix' E.toLinearMap
  have hQL : Q * L = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  have hLQ : L.conjTranspose * Q.conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, hQL, Matrix.conjTranspose_one]
  change (Q.conjTranspose * h * Q) *ᵥ ψ = 0 ↔ _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  change Q.conjTranspose *ᵥ (h *ᵥ E.symm ψ) = 0 ↔ h *ᵥ E.symm ψ = 0
  constructor
  · intro hz
    have hz' := congrArg (fun φ => L.conjTranspose *ᵥ φ) hz
    rw [Matrix.mulVec_mulVec, hLQ, Matrix.one_mulVec, Matrix.mulVec_zero] at hz'
    exact hz'
  · intro hz
    rw [hz, Matrix.mulVec_zero]

/-- An arbitrary positive parent interaction transports to a parent interaction
for the deformed tensor. Source: regional-kernel construction in
arXiv:2011.12127, Section IV.C.1, lines 2003–2011. -/
theorem IsRegionParentInteraction.physicalDeform (A : Tensor Γ d) (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ))
    {h : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ}
    (hh : IsRegionParentInteraction A R h) :
    IsRegionParentInteraction
      (TNLean.PEPS.physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)) R
      (deformedRegionInteraction R F h) := by
  refine ⟨deformedRegionInteraction_posSemidef R F hh.1, ?_⟩
  ext ψ
  change deformedRegionInteraction R F h *ᵥ ψ = 0 ↔ _
  rw [deformedRegionInteraction_mulVec_eq_zero_iff]
  change (regionPhysicalEquiv R F).symm ψ ∈ (Matrix.mulVecLin h).ker ↔ _
  rw [hh.2]
  simpa only [LinearEquiv.apply_symm_apply] using
    (regionPhysicalEquiv_mem_regionGroundSpace_iff A R F ((regionPhysicalEquiv R F).symm ψ)).symm

end TNLean.PEPS
