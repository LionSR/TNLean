/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.ThreeBlockOpenBoundaryLocalization

/-!
# The actual eight-leg three-block open contraction

Only the twelve incidences at the three physical tensors are summed. The
boundary tensor is an arbitrary function of the eight exterior virtual legs.
Summing the auxiliary exterior endpoints in a graph cut gives exactly this
range; conversely a fixed auxiliary configuration realizes every such boundary.

Source: SCP10, arXiv:1001.3807, Theorem 5.4.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.ThreeBlockDependent
open DependentBondNetwork

/-- The twelve virtual incidences at the three core tensors. -/
abbrev CoreEndpoint := {p : Endpoint Bond // endpointVertex tail head p ∈ coreVertices}

/-- The eight auxiliary endpoints opposite the open virtual legs. -/
abbrev ExteriorEndpoint := {p : Endpoint Bond // endpointVertex tail head p ∉ coreVertices}

/-- Each independently sized exterior virtual leg appears exactly once. -/
abbrev OpenBoundaryConfig (D : Bond → Type*) := (e : {e // e ∈ exteriorBonds}) → D e.1

/-- Independent coordinates at the core tensor incidences. -/
abbrev CoreEndpointConfig (D : Bond → Type*) := (p : CoreEndpoint) → D p.1.1

/-- Independent coordinates at the auxiliary endpoints. -/
abbrev ExteriorEndpointConfig (D : Bond → Type*) := (p : ExteriorEndpoint) → D p.1.1

/-- Every tail belongs to one of the three physical tensors. -/
theorem tail_mem_core (e : Bond) : tail e ∈ coreVertices := by
  revert e
  decide

/-- Precisely the two internal edges have heads in the core. -/
theorem head_mem_core_iff (e : Bond) : head e ∈ coreVertices ↔ e ∉ exteriorBonds := by
  revert e
  decide

/-- An endpoint outside the core lies on an exterior edge. -/
theorem exteriorEndpoint_mem_exterior (p : ExteriorEndpoint) : p.1.1 ∈ exteriorBonds := by
  have h : ∀ p : Endpoint Bond,
      endpointVertex tail head p ∉ coreVertices → p.1 ∈ exteriorBonds := by decide
  exact h p.1 p.2

/-- Three four-legged tensors have twelve core incidences. -/
theorem coreEndpoint_card : Fintype.card CoreEndpoint = 12 := by decide

/-- The auxiliary graph contains exactly eight exterior endpoints. -/
theorem exteriorEndpoint_card : Fintype.card ExteriorEndpoint = 8 := by decide

variable (D : Bond → Type*)

/-- Assemble independent core and auxiliary endpoint configurations. -/
def assembleCoreEndpointConfig (η : CoreEndpointConfig D) (ξ : ExteriorEndpointConfig D) :
    EndpointConfig D :=
  fun p ↦ if hp : endpointVertex tail head p ∈ coreVertices then η ⟨p, hp⟩ else ξ ⟨p, hp⟩

/-- Retain the eight exterior virtual coordinates belonging to the core. -/
def openBoundaryRestriction (η : CoreEndpointConfig D) : OpenBoundaryConfig D :=
  fun e ↦ η ⟨(e.1, false), tail_mem_core e.1⟩

/-- Recover the local four virtual coordinates at a core vertex. -/
def coreEndpointLocalConfig (η : CoreEndpointConfig D) (v : CoreVertex) :
    LocalConfig D v.1 :=
  fun p ↦ η ⟨p.1, by rw [p.2]; exact v.2⟩

/-- A doubled exterior cut consists of the eight open core labels and eight
independent auxiliary labels. -/
def assembleExteriorCutConfig (θ : OpenBoundaryConfig D) (ξ : ExteriorEndpointConfig D) :
    CutConfig exteriorBonds D :=
  fun p ↦ if p.2 then
    ξ ⟨(p.1.1, true), by
      change head p.1.1 ∉ coreVertices
      rw [head_mem_core_iff]
      exact not_not.mpr p.1.2⟩
    else θ p.1

/-- Extract the eight auxiliary endpoint labels from the doubled cut. -/
def exteriorCutRestriction (θ : CutConfig exteriorBonds D) : ExteriorEndpointConfig D :=
  fun p ↦ θ (⟨p.1.1, exteriorEndpoint_mem_exterior p⟩, p.1.2)

/-- The doubled exterior cut is exactly the assembled open and auxiliary boundary. -/
theorem cutRestriction_assembleCoreEndpointConfig
    (η : CoreEndpointConfig D) (ξ : ExteriorEndpointConfig D) :
    cutRestriction D exteriorBonds (assembleCoreEndpointConfig D η ξ) =
      assembleExteriorCutConfig D (openBoundaryRestriction D η) ξ := by
  funext p
  rcases p with ⟨e, b⟩
  cases b
  · simp [cutRestriction, assembleCoreEndpointConfig, assembleExteriorCutConfig,
      endpointVertex, tail_mem_core, openBoundaryRestriction]
  · simp [cutRestriction, assembleCoreEndpointConfig, assembleExteriorCutConfig,
      endpointVertex, head_mem_core_iff, e.2]

/-- Extracting the auxiliary labels after assembling a doubled boundary recovers them. -/
@[simp]
theorem exteriorCutRestriction_assemble (θ : OpenBoundaryConfig D)
    (ξ : ExteriorEndpointConfig D) :
    exteriorCutRestriction D (assembleExteriorCutConfig D θ ξ) = ξ := by
  funext p
  rcases p with ⟨⟨e, b⟩, hp⟩
  cases b
  · exact False.elim (hp (tail_mem_core e))
  · simp [exteriorCutRestriction, assembleExteriorCutConfig]

variable [∀ e, DecidableEq (D e)]
variable {Phys : Vertex → Type*}

/-- Identity contractions on the two internal bonds, with no exterior factors. -/
def coreInteriorWeight (η : CoreEndpointConfig D) : ℂ :=
  ∏ e, if he : e ∈ exteriorBonds then 1 else
    (1 : Matrix (D e) (D e) ℂ)
      (η ⟨(e, true), (head_mem_core_iff e).mpr he⟩)
      (η ⟨(e, false), tail_mem_core e⟩)

/-- The graph's internal contraction ignores all auxiliary endpoint coordinates. -/
theorem cutInteriorWeight_assembleCoreEndpointConfig
    (η : CoreEndpointConfig D) (ξ : ExteriorEndpointConfig D) :
    cutInteriorWeight D exteriorBonds (assembleCoreEndpointConfig D η ξ) =
      coreInteriorWeight D η := by
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : e ∈ exteriorBonds
  · simp [he]
  · simp only [he, ↓reduceIte]
    have hh : assembleCoreEndpointConfig D η ξ (e, true) =
        η ⟨(e, true), (head_mem_core_iff e).mpr he⟩ := by
      simp [assembleCoreEndpointConfig, endpointVertex, head_mem_core_iff, he]
    have ht : assembleCoreEndpointConfig D η ξ (e, false) =
        η ⟨(e, false), tail_mem_core e⟩ := by
      simp [assembleCoreEndpointConfig, endpointVertex, tail_mem_core]
    rw [hh, ht]
    rfl

omit [∀ e, DecidableEq (D e)] in
/-- A core tensor only sees its own four core incidences. -/
@[simp]
theorem endpointSiteEquiv_assembleCoreEndpointConfig
    (η : CoreEndpointConfig D) (ξ : ExteriorEndpointConfig D) (v : CoreVertex) :
    endpointSiteEquiv tail head D (assembleCoreEndpointConfig D η ξ) v.1 =
      coreEndpointLocalConfig D η v := by
  funext p
  have hp : endpointVertex tail head p.1 ∈ coreVertices := by rw [p.2]; exact v.2
  simp [assembleCoreEndpointConfig, coreEndpointLocalConfig, hp]

variable [∀ e, Fintype (D e)]

/-- Literal contraction of three four-legged tensors against one arbitrary
joint eight-virtual-leg boundary. -/
def openBoundaryCoeff
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (M : OpenBoundaryConfig D → ℂ) (σ : CorePhysicalConfig Phys) : ℂ :=
  ∑ η : CoreEndpointConfig D,
    (M (openBoundaryRestriction D η) * coreInteriorWeight D η) *
      ∏ v : CoreVertex, A v.1 (coreEndpointLocalConfig D η v) (σ v)

/-- The eight-virtual-leg open contraction map has exactly three physical factors. -/
def openBoundaryMap
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ) :
    (OpenBoundaryConfig D → ℂ) →ₗ[ℂ] (CorePhysicalConfig Phys → ℂ) where
  toFun := openBoundaryCoeff D A
  map_add' M N := by
    funext σ
    simp [openBoundaryCoeff, add_mul, Finset.sum_add_distrib]
  map_smul' z M := by
    funext σ
    simp [openBoundaryCoeff, mul_assoc, Finset.mul_sum]

/-- The whole three-block open-boundary range. -/
def openBoundarySpace (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ) :
    Submodule ℂ (CorePhysicalConfig Phys → ℂ) := (openBoundaryMap D A).range

/-- The whole core has no omitted core physical factors. -/
def emptyOutsideCorePhysicalConfig : OutsideCorePhysicalConfig coreVertices Phys :=
  fun v ↦ False.elim (v.2.2 v.2.1)

/-- Sum the eight auxiliary endpoint coordinates of a joint cut boundary. -/
def openBoundaryMarginal
    (M : CutConfig exteriorBonds D × OutsideCorePhysicalConfig coreVertices Phys → ℂ)
    (θ : OpenBoundaryConfig D) : ℂ :=
  ∑ ξ : ExteriorEndpointConfig D,
    M (assembleExteriorCutConfig D θ ξ, emptyOutsideCorePhysicalConfig)

omit [∀ e, DecidableEq (D e)] in
/-- Endpoint summation separates into twelve core and eight auxiliary coordinates. -/
theorem sum_endpoint_eq_sum_core_exterior (f : EndpointConfig D → ℂ) :
    (∑ β, f β) = ∑ η : CoreEndpointConfig D, ∑ ξ : ExteriorEndpointConfig D,
      f (assembleCoreEndpointConfig D η ξ) := by
  rw [← (Equiv.piEquivPiSubtypeProd (fun p : Endpoint Bond ↦
    endpointVertex tail head p ∈ coreVertices) (fun p ↦ D p.1)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

/-- The graph cut contracts to the eight-leg open boundary obtained by summing
its auxiliary coordinates. No factorization of the joint boundary is assumed. -/
theorem coreLiftedCutMap_eq_openBoundaryMap
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (M : CutConfig exteriorBonds D × OutsideCorePhysicalConfig coreVertices Phys → ℂ) :
    coreLiftedCutMap D A coreVertices (Finset.Subset.refl _) exteriorBonds M =
      openBoundaryMap D A (openBoundaryMarginal D M) := by
  funext σ
  have hempty : (fun v : {v : Vertex // v ∈ coreVertices ∧ v ∉ coreVertices} ↦
      σ ⟨v.1, v.2.1⟩) = (emptyOutsideCorePhysicalConfig (Phys := Phys)) := by
    funext v
    exact False.elim (v.2.2 v.2.1)
  simp only [coreLiftedCutMap, coreLiftedCutCoeff, openBoundaryMap,
    openBoundaryCoeff, LinearMap.coe_mk, AddHom.coe_mk, hempty]
  rw [sum_endpoint_eq_sum_core_exterior]
  simp only [cutRestriction_assembleCoreEndpointConfig,
    cutInteriorWeight_assembleCoreEndpointConfig, endpointSiteEquiv_assembleCoreEndpointConfig]
  simp only [openBoundaryMarginal, Finset.sum_mul]

/-- A doubled cut boundary supported at one auxiliary configuration realizes
any prescribed, fully correlated eight-leg boundary. -/
def fixedExteriorCutBoundary (ξ₀ : ExteriorEndpointConfig D)
    (M : OpenBoundaryConfig D → ℂ) :
    CutConfig exteriorBonds D × OutsideCorePhysicalConfig coreVertices Phys → ℂ :=
  fun p ↦ M (fun e ↦ p.1 (e, false)) *
    (Pi.single ξ₀ (1 : ℂ) : ExteriorEndpointConfig D → ℂ) (exteriorCutRestriction D p.1)

/-- Summing a fixed auxiliary boundary recovers precisely the prescribed
arbitrary eight-leg boundary. -/
@[simp]
theorem openBoundaryMarginal_fixedExteriorCutBoundary
    (ξ₀ : ExteriorEndpointConfig D) (M : OpenBoundaryConfig D → ℂ) :
    openBoundaryMarginal D (fixedExteriorCutBoundary (Phys := Phys) D ξ₀ M) = M := by
  classical
  funext θ
  simp [openBoundaryMarginal, fixedExteriorCutBoundary, assembleExteriorCutConfig,
    Pi.single_apply]

/-- The full three-core contraction range has exactly eight arbitrary exterior
virtual legs and exactly three physical factors. -/
theorem coreLiftedCutSpace_eq_openBoundarySpace
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (ξ₀ : ExteriorEndpointConfig D) :
    coreLiftedCutSpace D A coreVertices (Finset.Subset.refl _) exteriorBonds =
      openBoundarySpace D A := by
  apply le_antisymm
  · rintro _ ⟨M, rfl⟩
    exact ⟨openBoundaryMarginal D M, (coreLiftedCutMap_eq_openBoundaryMap D A M).symm⟩
  · rintro _ ⟨M, rfl⟩
    refine ⟨fixedExteriorCutBoundary D ξ₀ M, ?_⟩
    rw [coreLiftedCutMap_eq_openBoundaryMap, openBoundaryMarginal_fixedExteriorCutBoundary]

end TNLean.PEPS.ThreeBlockDependent
