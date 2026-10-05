/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOrientedAveragingBondState
import TNLean.PEPS.GraphRepeatedParentSupport

/-!
# Canonical parent bond support for arbitrary edge orientations

The actual open-region internal factors are weighted relative representation
matrices. Reversing a native edge reverses the relative group element and
transposes its ordered physical endpoint pair. Support for both single-bond
matrix orders therefore gives support for every actual internal slice, with
all crossing factors retained. Edge-covering canonical parent constraints then
imply the full physical product range without a ground-space equality hypothesis.

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

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- A native internal factor has the prescribed single-bond support in
both possible orientations. Source: SCP10, Section 7, lines 2977–3019. -/
theorem graphOrientedOpenInternalFactor_mem_range_of_factors
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (o : Edge Γ → Bool)
    (F : Matrix (X × X) Z ℂ)
    (hF : ∀ g, (fun r : X × X => (W ^ 2 * U g) r.1 r.2) ∈ (Matrix.mulVecLin F).range)
    (hFt : ∀ g, (fun r : X × X => (W ^ 2 * U g) r.2 r.1) ∈ (Matrix.mulVecLin F).range)
    (R : Finset V) (q : RV R → G) (f : RI (Γ := Γ) R) :
    graphOrientedOpenInternalFactor U W o R q f ∈ (Matrix.mulVecLin F).range := by
  unfold graphOrientedOpenInternalFactor
  cases ho : o f.1
  · simpa only [graphOrientedOpenInternalFactor, ho, Bool.false_eq_true, ↓reduceIte] using
      hF (q ⟨f.1.1.2, f.2.2⟩ * (q ⟨f.1.1.1, f.2.1⟩)⁻¹)
  · simpa only [graphOrientedOpenInternalFactor, ho, ↓reduceIte] using
      hFt (q ⟨f.1.1.1, f.2.1⟩ * (q ⟨f.1.1.2, f.2.2⟩)⁻¹)

/-- Fixing the physical crossing endpoints in the actual oriented open
contraction leaves the coherent product of its derived internal factors.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem graphRegionInternalBondSlice_orientedAveragingSite
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (o : Edge Γ → Bool) (R : Finset V) (θ σ : RB (Γ := Γ) R → X) :
    graphRegionInternalBondSlice R σ
      (graphOpenRegionNetwork (graphOrientedAveragingSite U W o) R θ) =
      fun β => ∑ q : RV R → G, (Fintype.card G : ℂ)⁻¹ ^ R.card *
        (∏ f : RB (Γ := Γ) R, graphOrientedOpenBoundaryFactor U W o R q f (θ f) (σ f)) *
        ∏ f : RI (Γ := Γ) R, graphOrientedOpenInternalFactor U W o R q f (β f) := by
  funext β
  change graphOpenRegionNetwork (graphOrientedAveragingSite U W o) R θ
    ((regionHalfEdgeLabelEquiv R).symm
      (σ, (fun f => (β f).2), fun f => (β f).1)) = _
  rw [graphOpenBondRegrouping_orientedAveragingSite U W hc o R θ (σ, β),
    graphOrientedOpenBondCoordinates_eq_sum_prod]

/-- Every actual oriented open contraction inherits internal product support
from both matrix orders of its weighted relative representation factors, for
arbitrary retained virtual and physical crossing labels. -/
theorem graphRegionInternalBondSlice_mem_range_of_oriented_factors
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (o : Edge Γ → Bool) (F : Matrix (X × X) Z ℂ)
    (hF : ∀ g, (fun r : X × X => (W ^ 2 * U g) r.1 r.2) ∈ (Matrix.mulVecLin F).range)
    (hFt : ∀ g, (fun r : X × X => (W ^ 2 * U g) r.2 r.1) ∈ (Matrix.mulVecLin F).range)
    (R : Finset V) (θ σ : RB (Γ := Γ) R → X) :
    graphRegionInternalBondSlice R σ
      (graphOpenRegionNetwork (graphOrientedAveragingSite U W o) R θ) ∈
        LinearMap.range (physicalProductMap (RI (Γ := Γ) R) F) := by
  classical
  have hf : ∀ (q : RV R → G) (f : RI (Γ := Γ) R),
      ∃ x, Matrix.mulVecLin F x = graphOrientedOpenInternalFactor U W o R q f := by
    intro q f
    exact graphOrientedOpenInternalFactor_mem_range_of_factors U W o F hF hFt R q f
  choose x hx using hf
  rw [graphRegionInternalBondSlice_orientedAveragingSite U W hc]
  let c (q : RV R → G) : ℂ := (Fintype.card G : ℂ)⁻¹ ^ R.card *
    ∏ f : RB (Γ := Γ) R, graphOrientedOpenBoundaryFactor U W o R q f (θ f) (σ f)
  refine ⟨fun β => ∑ q : RV R → G, c q * ∏ f, x q f (β f), ?_⟩
  exact physicalProductMap_sum_prod_eq F c (fun f q => x q f)
    (fun f q => graphOrientedOpenInternalFactor U W o R q f) (fun f q => hx q f)

/-- Every vector in the genuine oriented regional PEPS range has the
prescribed internal product support, derived from every open boundary column. -/
theorem regionInternalBondSlice_mem_range_of_oriented_factors {p : ℕ}
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (o : Edge Γ → Bool) (F : Matrix (X × X) Z ℂ)
    (hF : ∀ g, (fun r : X × X => (W ^ 2 * U g) r.1 r.2) ∈ (Matrix.mulVecLin F).range)
    (hFt : ∀ g, (fun r : X × X => (W ^ 2 * U g) r.2 r.1) ∈ (Matrix.mulVecLin F).range)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (R : Finset V) (σ : RB (Γ := Γ) R → X)
    {ψ : RegionPhysicalConfig (d := p) R → ℂ}
    (hψ : ψ ∈ regionGroundSpace (numberedGraphOrientedAveragingTensor U W o e) R) :
    regionInternalBondSlice e R σ ψ ∈ LinearMap.range
      (physicalProductMap (RI (Γ := Γ) R) F) := by
  classical
  let A := numberedGraphOrientedAveragingTensor U W o e
  let S := LinearMap.range (physicalProductMap (RI (Γ := Γ) R) F)
  have hle : regionGroundSpace A R ≤ S.comap (regionInternalBondSlice e R σ) := by
    apply (regionGroundSpace_le_iff A R _).mpr
    intro μ
    let θ : RB (Γ := Γ) R → X := fun f => (Fintype.equivFin X).symm (μ f)
    have hμ : (fun f => Fintype.equivFin X (θ f)) = μ := by
      funext f
      exact Equiv.apply_symm_apply _ _
    change regionInternalBondSlice e R σ (openRegionWeight A R μ) ∈ S
    rw [← hμ]
    change regionInternalBondSlice e R σ
      (openRegionWeight (groupBondTensor
        (fun v η s => graphOrientedAveragingSite U W o v η ((e v).symm s)))
        R (fun f => Fintype.equivFin X (θ f))) ∈ S
    rw [regionInternalBondSlice_openRegionWeight]
    exact graphRegionInternalBondSlice_mem_range_of_oriented_factors U W hc o F hF hFt R θ σ
  exact hle hψ

/-- Support for the actual oriented single-bond factors and edge-covering
canonical parent constraints give full physical product support for every
parent ground vector. Source: SCP10, Theorem 5.7 and Section 7, lines 2977–3019. -/
theorem regionParentGroundSpace_mem_product_range_of_oriented_factors {p : ℕ}
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (o : Edge Γ → Bool) (F : Matrix (X × X) Z ℂ)
    (hF : ∀ g, (fun r : X × X => (W ^ 2 * U g) r.1 r.2) ∈ (Matrix.mulVecLin F).range)
    (hFt : ∀ g, (fun r : X × X => (W ^ 2 * U g) r.2 r.1) ∈ (Matrix.mulVecLin F).range)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    {ψ : (V → Fin p) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace (numberedGraphOrientedAveragingTensor U W o e) R) :
    (fun β => ψ (fun v => e v (graphSiteBondEndpointEquiv.symm β v))) ∈
      LinearMap.range (physicalProductMap (Edge Γ) F) :=
  regionParentGroundSpace_mem_product_range_of_internal_slices _ e F R hcover
    (fun i σ _φ hφ => regionInternalBondSlice_mem_range_of_oriented_factors
      U W hc o F hF hFt e (R i) σ hφ) hψ

end TNLean.PEPS
