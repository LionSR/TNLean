/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.ThreeBlockOpenBoundaryContraction

/-!
# Minimally indexed regional open contractions

A regional boundary has one virtual coordinate for each cut incidence belonging
to the region. The omitted core physical coordinate remains freely correlated
with all these virtual indices. Summing the complementary graph endpoints gives
exactly this contraction; fixing those endpoints realizes every boundary.

For either two-core region of SCP10, arXiv:1001.3807, Theorem 5.4, this is a
six-virtual-leg boundary and one unrestricted complementary physical factor.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.ThreeBlockDependent
open DependentBondNetwork

/-- Virtual incidences at the tensors belonging to a region. -/
abbrev RegionEndpoint (R : Finset Vertex) :=
  {p : Endpoint Bond // endpointVertex tail head p ∈ R}

/-- Graph endpoints outside the selected region. -/
abbrev OutsideRegionEndpoint (R : Finset Vertex) :=
  {p : Endpoint Bond // endpointVertex tail head p ∉ R}

/-- Exactly the cut virtual incidences at regional tensors. -/
abbrev RegionBoundaryEndpoint (R : Finset Vertex) (C : Finset Bond) :=
  {p : Endpoint Bond // endpointVertex tail head p ∈ R ∧ p.1 ∈ C}

/-- Virtual labels on the regional tensor incidences. -/
abbrev RegionEndpointConfig (D : Bond → Type*) (R : Finset Vertex) :=
  (p : RegionEndpoint R) → D p.1.1

/-- Virtual labels on the complementary graph endpoints. -/
abbrev OutsideRegionEndpointConfig (D : Bond → Type*) (R : Finset Vertex) :=
  (p : OutsideRegionEndpoint R) → D p.1.1

/-- A minimally indexed, arbitrarily correlated regional virtual boundary. -/
abbrev RegionBoundaryConfig (D : Bond → Type*) (R : Finset Vertex) (C : Finset Bond) :=
  (p : RegionBoundaryEndpoint R C) → D p.1.1

/-- The left two-core range has exactly six exposed virtual incidences. -/
theorem left_regionBoundary_card :
    Fintype.card (RegionBoundaryEndpoint {0, 1} leftCut) = 6 := by decide

/-- The right two-core range has exactly six exposed virtual incidences. -/
theorem right_regionBoundary_card :
    Fintype.card (RegionBoundaryEndpoint {1, 2} rightCut) = 6 := by decide

variable (D : Bond → Type*)

/-- Assemble regional and complementary endpoint labels. -/
def assembleRegionEndpointConfig (R : Finset Vertex)
    (η : RegionEndpointConfig D R) (ξ : OutsideRegionEndpointConfig D R) :
    EndpointConfig D :=
  fun p ↦ if hp : endpointVertex tail head p ∈ R then η ⟨p, hp⟩ else ξ ⟨p, hp⟩

/-- Restrict regional tensor coordinates to the cut incidences only. -/
def regionBoundaryRestriction (R : Finset Vertex) (C : Finset Bond)
    (η : RegionEndpointConfig D R) : RegionBoundaryConfig D R C :=
  fun p ↦ η ⟨p.1, p.2.1⟩

/-- Read the four local virtual labels at a regional tensor. -/
def regionEndpointLocalConfig (R : Finset Vertex) (η : RegionEndpointConfig D R)
    (v : {v : Vertex // v ∈ R}) : LocalConfig D v.1 :=
  fun p ↦ η ⟨p.1, by rw [p.2]; exact v.2⟩

/-- Assemble the doubled graph cut from its actual regional boundary and
independent complementary graph endpoint labels. -/
def assembleRegionalCutConfig (R : Finset Vertex) (C : Finset Bond)
    (θ : RegionBoundaryConfig D R C) (ξ : OutsideRegionEndpointConfig D R) :
    CutConfig C D :=
  fun p ↦ if hp : endpointVertex tail head (p.1.1, p.2) ∈ R then
    θ ⟨(p.1.1, p.2), hp, p.1.2⟩ else ξ ⟨(p.1.1, p.2), hp⟩

/-- Restrict a doubled graph cut to its actual regional boundary. -/
def regionalCutBoundaryRestriction (R : Finset Vertex) (C : Finset Bond)
    (θ : CutConfig C D) : RegionBoundaryConfig D R C :=
  fun p ↦ θ (⟨p.1.1, p.2.2⟩, p.1.2)

/-- Every complementary graph endpoint is cut when all uncut edges lie internally. -/
def outsideRegionalCutRestriction (R : Finset Vertex) (C : Finset Bond)
    (hC : ∀ p : Endpoint Bond, p.1 ∉ C → endpointVertex tail head p ∈ R)
    (θ : CutConfig C D) : OutsideRegionEndpointConfig D R :=
  fun p ↦ θ (⟨p.1.1, by
    by_contra hp
    exact p.2 (hC p.1 hp)⟩, p.1.2)

/-- The graph cut of assembled endpoint labels is the assembled regional cut. -/
theorem cutRestriction_assembleRegionEndpointConfig (R : Finset Vertex) (C : Finset Bond)
    (η : RegionEndpointConfig D R) (ξ : OutsideRegionEndpointConfig D R) :
    cutRestriction D C (assembleRegionEndpointConfig D R η ξ) =
      assembleRegionalCutConfig D R C (regionBoundaryRestriction D R C η) ξ := by
  funext p
  rfl

/-- Reading the actual regional boundary after assembly recovers it. -/
@[simp]
theorem regionalCutBoundaryRestriction_assemble (R : Finset Vertex) (C : Finset Bond)
    (θ : RegionBoundaryConfig D R C) (ξ : OutsideRegionEndpointConfig D R) :
    regionalCutBoundaryRestriction D R C (assembleRegionalCutConfig D R C θ ξ) = θ := by
  funext p
  simp [regionalCutBoundaryRestriction, assembleRegionalCutConfig, p.2.1]

/-- Reading the complementary labels after assembly recovers them. -/
@[simp]
theorem outsideRegionalCutRestriction_assemble (R : Finset Vertex) (C : Finset Bond)
    (hC : ∀ p : Endpoint Bond, p.1 ∉ C → endpointVertex tail head p ∈ R)
    (θ : RegionBoundaryConfig D R C) (ξ : OutsideRegionEndpointConfig D R) :
    outsideRegionalCutRestriction D R C hC (assembleRegionalCutConfig D R C θ ξ) = ξ := by
  funext p
  simp [outsideRegionalCutRestriction, assembleRegionalCutConfig, p.2]

/-- Regional tensor coordinates are independent of all complementary endpoint labels. -/
@[simp]
theorem endpointSiteEquiv_assembleRegionEndpointConfig (R : Finset Vertex)
    (η : RegionEndpointConfig D R) (ξ : OutsideRegionEndpointConfig D R)
    (v : {v : Vertex // v ∈ R}) :
    endpointSiteEquiv tail head D (assembleRegionEndpointConfig D R η ξ) v.1 =
      regionEndpointLocalConfig D R η v := by
  funext p
  have hp : endpointVertex tail head p.1 ∈ R := by rw [p.2]; exact v.2
  simp [assembleRegionEndpointConfig, regionEndpointLocalConfig, hp]

variable [∀ e, DecidableEq (D e)]

/-- Identity factors on precisely the internal uncut bonds of a region. -/
def regionInteriorWeight (R : Finset Vertex) (C : Finset Bond)
    (hC : ∀ p : Endpoint Bond, p.1 ∉ C → endpointVertex tail head p ∈ R)
    (η : RegionEndpointConfig D R) : ℂ :=
  ∏ e, if he : e ∈ C then 1 else
    (1 : Matrix (D e) (D e) ℂ)
      (η ⟨(e, true), hC (e, true) he⟩) (η ⟨(e, false), hC (e, false) he⟩)

/-- Uncut identity factors only involve the regional endpoint labels. -/
theorem cutInteriorWeight_assembleRegionEndpointConfig (R : Finset Vertex) (C : Finset Bond)
    (hC : ∀ p : Endpoint Bond, p.1 ∉ C → endpointVertex tail head p ∈ R)
    (η : RegionEndpointConfig D R) (ξ : OutsideRegionEndpointConfig D R) :
    cutInteriorWeight D C (assembleRegionEndpointConfig D R η ξ) =
      regionInteriorWeight D R C hC η := by
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : e ∈ C
  · simp [he]
  · simp only [he, ↓reduceIte]
    have hh : assembleRegionEndpointConfig D R η ξ (e, true) =
        η ⟨(e, true), hC (e, true) he⟩ := by
      simp [assembleRegionEndpointConfig, hC (e, true) he]
    have ht : assembleRegionEndpointConfig D R η ξ (e, false) =
        η ⟨(e, false), hC (e, false) he⟩ := by
      simp [assembleRegionEndpointConfig, hC (e, false) he]
    rw [hh, ht]
    rfl

variable [∀ e, Fintype (D e)]
variable {Phys : Vertex → Type*}

/-- A minimal regional open contraction lifted only to the three core physical
factors, with free correlations between its boundary and omitted core outputs. -/
def regionalBoundaryCoeff
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (R : Finset Vertex) (hR : R ⊆ coreVertices) (C : Finset Bond)
    (hC : ∀ p : Endpoint Bond, p.1 ∉ C → endpointVertex tail head p ∈ R)
    (M : RegionBoundaryConfig D R C × OutsideCorePhysicalConfig R Phys → ℂ)
    (σ : CorePhysicalConfig Phys) : ℂ :=
  ∑ η : RegionEndpointConfig D R,
    (M (regionBoundaryRestriction D R C η, fun v ↦ σ ⟨v.1, v.2.1⟩) *
      regionInteriorWeight D R C hC η) *
      ∏ v : {v : Vertex // v ∈ R},
        A v.1 (regionEndpointLocalConfig D R η v) (σ ⟨v.1, hR v.2⟩)

/-- The linear minimal regional open-boundary contraction map. -/
def regionalBoundaryMap
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (R : Finset Vertex) (hR : R ⊆ coreVertices) (C : Finset Bond)
    (hC : ∀ p : Endpoint Bond, p.1 ∉ C → endpointVertex tail head p ∈ R) :
    (RegionBoundaryConfig D R C × OutsideCorePhysicalConfig R Phys → ℂ) →ₗ[ℂ]
      (CorePhysicalConfig Phys → ℂ) where
  toFun := regionalBoundaryCoeff D A R hR C hC
  map_add' M N := by
    funext σ
    simp [regionalBoundaryCoeff, add_mul, Finset.sum_add_distrib]
  map_smul' z M := by
    funext σ
    simp [regionalBoundaryCoeff, mul_assoc, Finset.mul_sum]

/-- The actual lifted regional range with no auxiliary boundary coordinates. -/
def regionalBoundarySpace
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (R : Finset Vertex) (hR : R ⊆ coreVertices) (C : Finset Bond)
    (hC : ∀ p : Endpoint Bond, p.1 ∉ C → endpointVertex tail head p ∈ R) :
    Submodule ℂ (CorePhysicalConfig Phys → ℂ) :=
  (regionalBoundaryMap D A R hR C hC).range

/-- Sum every complementary virtual coordinate of an arbitrary doubled boundary. -/
def regionalBoundaryMarginal (R : Finset Vertex) (C : Finset Bond)
    (M : CutConfig C D × OutsideCorePhysicalConfig R Phys → ℂ)
    (p : RegionBoundaryConfig D R C × OutsideCorePhysicalConfig R Phys) : ℂ :=
  ∑ ξ : OutsideRegionEndpointConfig D R, M (assembleRegionalCutConfig D R C p.1 ξ, p.2)

omit [∀ e, DecidableEq (D e)] in
/-- Separate the regional and complementary independent endpoint sums. -/
theorem sum_endpoint_eq_sum_region_outside (R : Finset Vertex) (f : EndpointConfig D → ℂ) :
    (∑ β, f β) = ∑ η : RegionEndpointConfig D R, ∑ ξ : OutsideRegionEndpointConfig D R,
      f (assembleRegionEndpointConfig D R η ξ) := by
  rw [← (Equiv.piEquivPiSubtypeProd (fun p : Endpoint Bond ↦
    endpointVertex tail head p ∈ R) (fun p ↦ D p.1)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

/-- Marginalizing complementary virtual coordinates gives the literal minimal
regional contraction on the three core physical factors. -/
theorem coreLiftedCutMap_eq_regionalBoundaryMap
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (R : Finset Vertex) (hR : R ⊆ coreVertices) (C : Finset Bond)
    (hC : ∀ p : Endpoint Bond, p.1 ∉ C → endpointVertex tail head p ∈ R)
    (M : CutConfig C D × OutsideCorePhysicalConfig R Phys → ℂ) :
    coreLiftedCutMap D A R hR C M =
      regionalBoundaryMap D A R hR C hC (regionalBoundaryMarginal D R C M) := by
  funext σ
  simp only [coreLiftedCutMap, coreLiftedCutCoeff, regionalBoundaryMap,
    regionalBoundaryCoeff, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_endpoint_eq_sum_region_outside D R]
  simp only [cutRestriction_assembleRegionEndpointConfig,
    cutInteriorWeight_assembleRegionEndpointConfig D R C hC,
    endpointSiteEquiv_assembleRegionEndpointConfig]
  simp only [regionalBoundaryMarginal, Finset.sum_mul]

/-- Fixing complementary endpoint labels embeds any joint minimal regional boundary. -/
def fixedOutsideRegionalBoundary (R : Finset Vertex) (C : Finset Bond)
    (hC : ∀ p : Endpoint Bond, p.1 ∉ C → endpointVertex tail head p ∈ R)
    (ξ₀ : OutsideRegionEndpointConfig D R)
    (M : RegionBoundaryConfig D R C × OutsideCorePhysicalConfig R Phys → ℂ) :
    CutConfig C D × OutsideCorePhysicalConfig R Phys → ℂ :=
  fun p ↦ M (regionalCutBoundaryRestriction D R C p.1, p.2) *
    (Pi.single ξ₀ (1 : ℂ) : OutsideRegionEndpointConfig D R → ℂ)
      (outsideRegionalCutRestriction D R C hC p.1)

/-- Marginalization recovers every boundary embedded at one complementary configuration. -/
@[simp]
theorem regionalBoundaryMarginal_fixedOutsideRegionalBoundary
    (R : Finset Vertex) (C : Finset Bond)
    (hC : ∀ p : Endpoint Bond, p.1 ∉ C → endpointVertex tail head p ∈ R)
    (ξ₀ : OutsideRegionEndpointConfig D R)
    (M : RegionBoundaryConfig D R C × OutsideCorePhysicalConfig R Phys → ℂ) :
    regionalBoundaryMarginal D R C (fixedOutsideRegionalBoundary D R C hC ξ₀ M) = M := by
  classical
  funext p
  simp [regionalBoundaryMarginal, fixedOutsideRegionalBoundary, Pi.single_apply]

/-- The auxiliary graph range is exactly the minimal regional range. -/
theorem coreLiftedCutSpace_eq_regionalBoundarySpace
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (R : Finset Vertex) (hR : R ⊆ coreVertices) (C : Finset Bond)
    (hC : ∀ p : Endpoint Bond, p.1 ∉ C → endpointVertex tail head p ∈ R)
    (ξ₀ : OutsideRegionEndpointConfig D R) :
    coreLiftedCutSpace D A R hR C = regionalBoundarySpace D A R hR C hC := by
  apply le_antisymm
  · rintro _ ⟨M, rfl⟩
    exact ⟨regionalBoundaryMarginal D R C M,
      (coreLiftedCutMap_eq_regionalBoundaryMap D A R hR C hC M).symm⟩
  · rintro _ ⟨M, rfl⟩
    refine ⟨fixedOutsideRegionalBoundary D R C hC ξ₀ M, ?_⟩
    rw [coreLiftedCutMap_eq_regionalBoundaryMap D A R hR C hC,
      regionalBoundaryMarginal_fixedOutsideRegionalBoundary]

end TNLean.PEPS.ThreeBlockDependent
