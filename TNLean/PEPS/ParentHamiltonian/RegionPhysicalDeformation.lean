/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionGroundSpace
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

open scoped BigOperators Matrix

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

/-- Invertible physical deformation preserves the dimension of every regional space.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem finrank_regionGroundSpace_physicalDeform (A : Tensor Γ d) (R : Finset V)
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) :
    Module.finrank ℂ
      (regionGroundSpace (physicalDeform A (fun v => LinearMap.toMatrix' (F v).toLinearMap)) R) =
      Module.finrank ℂ (regionGroundSpace A R) :=
  (regionGroundSpacePhysicalEquiv A R F).symm.finrank_eq

end TNLean.PEPS
