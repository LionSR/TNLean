/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.ThreeBlockDependentCutIntersection
import TNLean.PEPS.DependentLiftedCut

/-!
# Three-core physical localization

Regional contraction ranges are expressed on precisely the three core physical
factors. Constant extension in the auxiliary exterior physical coordinates
identifies these ranges with the inverse images of the graph-wide lifted ranges.
The virtual boundary is arbitrary and retains all correlations.

Source: SCP10, arXiv:1001.3807, Theorem 5.4.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.ThreeBlockDependent
open DependentBondNetwork

/-- The three physical sites of the open region. -/
abbrev CoreVertex := {v : Vertex // v ∈ coreVertices}

/-- Physical coordinates of the three core sites only. -/
abbrev CorePhysicalConfig (Phys : Vertex → Type*) := (v : CoreVertex) → Phys v.1

/-- Core physical factors omitted by a regional contraction. -/
abbrev OutsideCorePhysicalConfig (R : Finset Vertex) (Phys : Vertex → Type*) :=
  (v : {v : Vertex // v ∈ coreVertices ∧ v ∉ R}) → Phys v.1

/-- Forget the auxiliary exterior physical factors. -/
def corePhysicalRestriction {Phys : Vertex → Type*} (σ : (v : Vertex) → Phys v) :
    CorePhysicalConfig Phys := fun v ↦ σ v.1

/-- Extend a core vector constantly in the exterior physical coordinates. -/
def corePhysicalExtension (Phys : Vertex → Type*) :
    (CorePhysicalConfig Phys → ℂ) →ₗ[ℂ] (((v : Vertex) → Phys v) → ℂ) where
  toFun ψ σ := ψ (corePhysicalRestriction σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Assemble core coordinates with a chosen exterior physical configuration. -/
def assembleCorePhysicalConfig {Phys : Vertex → Type*}
    (σ : CorePhysicalConfig Phys) (τ : OutsidePhysicalConfig coreVertices Phys) :
    (v : Vertex) → Phys v :=
  fun v ↦ if hv : v ∈ coreVertices then σ ⟨v, hv⟩ else τ ⟨v, hv⟩

@[simp]
theorem corePhysicalRestriction_assemble {Phys : Vertex → Type*}
    (σ : CorePhysicalConfig Phys) (τ : OutsidePhysicalConfig coreVertices Phys) :
    corePhysicalRestriction (assembleCorePhysicalConfig σ τ) = σ := by
  funext v
  simp [corePhysicalRestriction, assembleCorePhysicalConfig, v.2]

/-- One exterior configuration is enough to recover every core vector. -/
theorem corePhysicalExtension_injective {Phys : Vertex → Type*}
    (τ : OutsidePhysicalConfig coreVertices Phys) :
    Function.Injective (corePhysicalExtension Phys) := by
  intro ψ χ h
  funext σ
  simpa [corePhysicalExtension] using
    congrFun h (assembleCorePhysicalConfig σ τ)

variable (D : Bond → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : Vertex → Type*}

/-- A literal regional contraction on the three physical core factors, with
one jointly correlated virtual and omitted-core-physical boundary. -/
def coreLiftedCutCoeff
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (R : Finset Vertex) (hR : R ⊆ coreVertices) (C : Finset Bond)
    (M : CutConfig C D × OutsideCorePhysicalConfig R Phys → ℂ)
    (σ : CorePhysicalConfig Phys) : ℂ :=
  ∑ β : EndpointConfig D,
    (M (cutRestriction D C β, fun v ↦ σ ⟨v.1, v.2.1⟩) * cutInteriorWeight D C β) *
      ∏ v : {v : Vertex // v ∈ R},
        A v.1 (endpointSiteEquiv tail head D β v.1) (σ ⟨v.1, hR v.2⟩)

/-- The core-only regional contraction map. -/
def coreLiftedCutMap
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (R : Finset Vertex) (hR : R ⊆ coreVertices) (C : Finset Bond) :
    (CutConfig C D × OutsideCorePhysicalConfig R Phys → ℂ) →ₗ[ℂ]
      (CorePhysicalConfig Phys → ℂ) where
  toFun := coreLiftedCutCoeff D A R hR C
  map_add' M N := by
    funext σ
    simp [coreLiftedCutCoeff, add_mul, Finset.sum_add_distrib]
  map_smul' z M := by
    funext σ
    simp [coreLiftedCutCoeff, mul_assoc, Finset.mul_sum]

/-- Actual regional ranges in the three-factor physical space. -/
def coreLiftedCutSpace
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (R : Finset Vertex) (hR : R ⊆ coreVertices) (C : Finset Bond) :
    Submodule ℂ (CorePhysicalConfig Phys → ℂ) :=
  (coreLiftedCutMap D A R hR C).range

/-- A core-only boundary extends to the graph by ignoring exterior physical
coordinates. The contraction itself is unchanged. -/
theorem corePhysicalExtension_coreLiftedCutMap
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (R : Finset Vertex) (hR : R ⊆ coreVertices) (C : Finset Bond)
    (M : CutConfig C D × OutsideCorePhysicalConfig R Phys → ℂ) :
    corePhysicalExtension Phys (coreLiftedCutMap D A R hR C M) =
      liftedCutMap tail head D A R C
        (fun p ↦ M (p.1, fun v ↦ p.2 ⟨v.1, v.2.2⟩)) := by
  funext σ
  simp only [corePhysicalExtension, coreLiftedCutMap, coreLiftedCutCoeff,
    liftedCutMap_apply, liftedCutCoeff, corePhysicalRestriction,
    outsidePhysicalRestriction, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro β _
  congr 1
  exact (Finset.prod_subtype R (fun _ ↦ Iff.rfl)
    (fun v ↦ A v (endpointSiteEquiv tail head D β v) (σ v))).symm

/-- Fixing auxiliary exterior coordinates turns any graph boundary into an
actual core-only boundary. -/
theorem coreLiftedCutMap_boundary_slice
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (R : Finset Vertex) (hR : R ⊆ coreVertices) (C : Finset Bond)
    (M : CutConfig C D × OutsidePhysicalConfig R Phys → ℂ)
    (τ : OutsidePhysicalConfig coreVertices Phys) (σ : CorePhysicalConfig Phys) :
    coreLiftedCutMap D A R hR C
      (fun p ↦ M (p.1, fun v ↦ if hv : v.1 ∈ coreVertices then
        p.2 ⟨v.1, hv, v.2⟩ else τ ⟨v.1, hv⟩)) σ =
      liftedCutMap tail head D A R C M (assembleCorePhysicalConfig σ τ) := by
  simp only [coreLiftedCutMap, coreLiftedCutCoeff, liftedCutMap_apply,
    liftedCutCoeff, assembleCorePhysicalConfig,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro β _
  congr 1
  rw [Finset.prod_subtype R (fun _ ↦ Iff.rfl)
    (fun v ↦ A v (endpointSiteEquiv tail head D β v)
      (if hv : v ∈ coreVertices then σ ⟨v, hv⟩ else τ ⟨v, hv⟩))]
  apply Finset.prod_congr rfl
  intro v _
  simp [hR v.2]

/-- Removing all auxiliary physical factors is an exact equality of ranges.
The conclusion is stated solely in the three-core physical space. -/
theorem comap_liftedCutSpace_eq_coreLiftedCutSpace
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (R : Finset Vertex) (hR : R ⊆ coreVertices) (C : Finset Bond)
    (τ : OutsidePhysicalConfig coreVertices Phys) :
    (liftedCutSpace tail head D A R C).comap (corePhysicalExtension Phys) =
      coreLiftedCutSpace D A R hR C := by
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨M, hM⟩ := hψ
    refine ⟨(fun p ↦ M (p.1, fun v ↦ if hv : v.1 ∈ coreVertices then
      p.2 ⟨v.1, hv, v.2⟩ else τ ⟨v.1, hv⟩)), ?_⟩
    funext σ
    rw [coreLiftedCutMap_boundary_slice, hM]
    simp [corePhysicalExtension]
  · rintro _ ⟨M, rfl⟩
    exact ⟨(fun p ↦ M (p.1, fun v ↦ p.2 ⟨v.1, v.2.2⟩)),
      (corePhysicalExtension_coreLiftedCutMap D A R hR C M).symm⟩

end TNLean.PEPS.ThreeBlockDependent
