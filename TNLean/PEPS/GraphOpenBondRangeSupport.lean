/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphRepeatedParentSupport

/-!
# Canonical parent bond support from actual internal factors

If every weighted relative representation matrix lies in a specified bond-map
range, then every actual open-region internal slice lies in its product range.
Edge-covering canonical parent regions consequently impose the full product
support on every global ground vector. The hypothesis concerns single-bond
matrices, not a global ground-space identity.

Source: SCP10, arXiv:1001.3807, regional contraction and Section 7,
lines 2977–3019.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R}
private abbrev RB (R : Finset V) := {f : Edge Γ // IsRegionBoundaryEdge R f}
variable {G X Z : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X] [Fintype Z]

/-- Actual open contractions inherit product support from their internal
weighted relative representation matrices, for arbitrary boundary labels. -/
theorem graphRegionInternalBondSlice_mem_range_of_factors
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (F : Matrix (X × X) Z ℂ)
    (hF : ∀ g, (fun r : X × X => (W ^ 2 * U g) r.1 r.2) ∈ (Matrix.mulVecLin F).range)
    (R : Finset V) (θ σ : RB (Γ := Γ) R → X) :
    graphRegionInternalBondSlice R σ
      (graphOpenRegionNetwork (graphDressedAveragingSite U W) R θ) ∈
        LinearMap.range (physicalProductMap (RI (Γ := Γ) R) F) := by
  classical
  change ∀ g, ∃ x, Matrix.mulVecLin F x = (fun r : X × X => (W ^ 2 * U g) r.1 r.2) at hF
  choose x hx using hF
  rw [graphRegionInternalBondSlice_dressedAveragingSite U W hc]
  let r (q : RV R → G) (e : RI (Γ := Γ) R) : G :=
    q ⟨e.1.1.2, e.2.2⟩ * (q ⟨e.1.1.1, e.2.1⟩)⁻¹
  refine ⟨fun β => ∑ q : RV R → G,
    graphOpenAveragingBoundaryCoefficient U W R θ σ q * ∏ e, x (r q e) (β e), ?_⟩
  apply physicalProductMap_sum_prod_eq F
    (graphOpenAveragingBoundaryCoefficient U W R θ σ)
    (fun e q => x (r q e)) (fun e q a => (W ^ 2 * U (r q e)) a.1 a.2)
  intro e q
  exact hx (r q e)

/-- Every vector in the genuine regional range has the prescribed internal
product support whenever the actual single-bond factors do. -/
theorem regionInternalBondSlice_mem_range_of_factors {p : ℕ}
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (F : Matrix (X × X) Z ℂ)
    (hF : ∀ g, (fun r : X × X => (W ^ 2 * U g) r.1 r.2) ∈ (Matrix.mulVecLin F).range)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (R : Finset V) (σ : RB (Γ := Γ) R → X)
    {ψ : RegionPhysicalConfig (d := p) R → ℂ}
    (hψ : ψ ∈ regionGroundSpace (groupBondTensor
      (fun v η s => graphDressedAveragingSite U W v η ((e v).symm s))) R) :
    regionInternalBondSlice e R σ ψ ∈ LinearMap.range
      (physicalProductMap (RI (Γ := Γ) R) F) := by
  classical
  let A := groupBondTensor (fun v η s => graphDressedAveragingSite U W v η ((e v).symm s))
  let S := LinearMap.range (physicalProductMap (RI (Γ := Γ) R) F)
  have hle : regionGroundSpace A R ≤ S.comap (regionInternalBondSlice e R σ) := by
    apply (regionGroundSpace_le_iff A R _).mpr
    intro μ
    let θ : RB (Γ := Γ) R → X := fun f => (Fintype.equivFin X).symm (μ f)
    have hμ : (fun f => Fintype.equivFin X (θ f)) = μ := by
      funext f
      exact Equiv.apply_symm_apply _ _
    change regionInternalBondSlice e R σ (openRegionWeight A R μ) ∈ S
    rw [← hμ, regionInternalBondSlice_openRegionWeight]
    exact graphRegionInternalBondSlice_mem_range_of_factors U W hc F hF R θ σ
  exact hle hψ

/-- Single-bond support and actual edge-covering regional conditions supply
full product support for every canonical parent ground vector. -/
theorem regionParentGroundSpace_mem_product_range_of_factors {p : ℕ}
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (F : Matrix (X × X) Z ℂ)
    (hF : ∀ g, (fun r : X × X => (W ^ 2 * U g) r.1 r.2) ∈ (Matrix.mulVecLin F).range)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    {ψ : (V → Fin p) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace (groupBondTensor
      (fun v η s => graphDressedAveragingSite U W v η ((e v).symm s))) R) :
    (fun β => ψ (fun v => e v (graphSiteBondEndpointEquiv.symm β v))) ∈
      LinearMap.range (physicalProductMap (Edge Γ) F) :=
  regionParentGroundSpace_mem_product_range_of_internal_slices _ e F R hcover
    (fun i σ _φ hφ => regionInternalBondSlice_mem_range_of_factors U W hc F hF e (R i) σ hφ) hψ

end TNLean.PEPS
