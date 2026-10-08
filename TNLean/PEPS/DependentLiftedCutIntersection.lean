/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentLiftedCutReconstruction

/-!
# Intersections of actual lifted regional ranges

Covering regions force the physical vector into every local tensor range.
Reconstruction then identifies their lifted intersection with the intersection
of full cut contractions. Genuine local G-injective inverses reduce all cuts
simultaneously to canonical averaging tensors, using the same inverse at each
site and retaining the complete correlated boundary at every cut.

Source: SCP10, arXiv:1001.3807, Theorem 5.4.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge : Type*} [Fintype Vertex] [Fintype Edge]
variable [DecidableEq Vertex] [DecidableEq Edge]
variable (tail head : Edge → Vertex) (D : Edge → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : Vertex → Type*} [∀ v, Finite (Phys v)]

/-- Under regional coverage, intersections of actual lifted spaces equal
intersections of full cut spaces. Surjective sites may be left uncovered. -/
theorem iInf_liftedCutSpace_eq_iInf_cutSpace
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    {ι : Type*} (R : ι → Finset Vertex) (C : ι → Finset Edge)
    (hcut : ∀ i (p : Endpoint Edge), endpointVertex tail head p ∉ R i → p.1 ∈ C i)
    (hcover : ∀ v, (∃ i, v ∈ R i) ∨ LinearMap.range (localSiteMap tail head D A v) = ⊤) :
    (⨅ i, liftedCutSpace tail head D A (R i) (C i)) =
      ⨅ i, cutSpace tail head D A (C i) := by
  apply le_antisymm
  · intro ψ hψ
    apply (Submodule.mem_iInf _).mpr
    intro i
    rw [cutSpace_eq_liftedCutSpace_inf_range_product tail head D A (R i) (C i) (hcut i)]
    exact ⟨(Submodule.mem_iInf _).mp hψ i,
      iInf_liftedCutSpace_le_range_product tail head D A R C hcover hψ⟩
  · exact iInf_mono fun i ↦ cutSpace_le_liftedCutSpace tail head D A (R i) (C i) (hcut i)

/-- If every omitted site tensor is surjective, a single lifted regional
space already equals its full cut space. -/
theorem liftedCutSpace_eq_cutSpace_of_cover_or_surjective
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R : Finset Vertex) (C : Finset Edge)
    (hcut : ∀ p : Endpoint Edge, endpointVertex tail head p ∉ R → p.1 ∈ C)
    (hcover : ∀ v, v ∈ R ∨ LinearMap.range (localSiteMap tail head D A v) = ⊤) :
    liftedCutSpace tail head D A R C = cutSpace tail head D A C := by
  have hcov : ∀ v, (∃ _ : Unit, v ∈ R) ∨
      LinearMap.range (localSiteMap tail head D A v) = ⊤ := by
    intro v
    rcases hcover v with hv | hv
    · exact Or.inl ⟨(), hv⟩
    · exact Or.inr hv
  simpa only [iInf_const] using iInf_liftedCutSpace_eq_iInf_cutSpace tail head D A
    (fun _ : Unit ↦ R) (fun _ : Unit ↦ C) (fun _ ↦ hcut) hcov

/-- The two-region form of lifted reconstruction allows independent joint
boundaries in the two memberships. -/
theorem liftedCutSpace_inf_eq_cutSpace_inf
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R S : Finset Vertex) (C E : Finset Edge)
    (hR : ∀ p : Endpoint Edge, endpointVertex tail head p ∉ R → p.1 ∈ C)
    (hS : ∀ p : Endpoint Edge, endpointVertex tail head p ∉ S → p.1 ∈ E)
    (hcover : ∀ v, v ∈ R ∨ v ∈ S ∨ LinearMap.range (localSiteMap tail head D A v) = ⊤) :
    liftedCutSpace tail head D A R C ⊓ liftedCutSpace tail head D A S E =
      cutSpace tail head D A C ⊓ cutSpace tail head D A E := by
  let regions : Bool → Finset Vertex := fun b ↦ if b then R else S
  let cuts : Bool → Finset Edge := fun b ↦ if b then C else E
  have hcuts : ∀ i (p : Endpoint Edge), endpointVertex tail head p ∉ regions i →
      p.1 ∈ cuts i := by
    intro i
    cases i
    · exact hS
    · exact hR
  have hcov : ∀ v, (∃ i, v ∈ regions i) ∨
      LinearMap.range (localSiteMap tail head D A v) = ⊤ := by
    intro v
    rcases hcover v with hv | hv | hv
    · exact Or.inl ⟨true, hv⟩
    · exact Or.inl ⟨false, hv⟩
    · exact Or.inr hv
  simpa only [iInf_bool_eq, regions, cuts, Bool.false_eq_true, ↓reduceIte] using
    iInf_liftedCutSpace_eq_iInf_cutSpace tail head D A regions cuts hcuts hcov

variable {G : Type*} [Group G] [Fintype G]

/-- One family of genuine local inverses reduces the actual lifted regional
intersection to the canonical intersection of full correlated cut ranges. -/
theorem iInf_liftedCutSpace_eq_map_representationAveragingSite
    {ι : Type*} (i₀ : ι)
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (ρ v) (localSiteMap tail head D A v))
    (R : ι → Finset Vertex) (C : ι → Finset Edge)
    (hcut : ∀ i (p : Endpoint Edge), endpointVertex tail head p ∉ R i → p.1 ∈ C i)
    (hcover : ∀ v, (∃ i, v ∈ R i) ∨ LinearMap.range (localSiteMap tail head D A v) = ⊤) :
    (⨅ i, liftedCutSpace tail head D A (R i) (C i)) =
      (⨅ i, cutSpace tail head D (representationAveragingSite tail head D ρ) (C i)).map
        (dependentPhysicalProductFamilyMap
          (fun v ↦ LinearMap.toMatrix' (localSiteMap tail head D A v))) := by
  rw [iInf_liftedCutSpace_eq_iInf_cutSpace tail head D A R C hcut hcover]
  exact iInf_cutSpace_eq_map_representationAveragingSite tail head D i₀ ρ A hA C

/-- The common local inverse comes with actual canonical membership and
reconstruction of every vector in the lifted regional intersection. -/
theorem exists_liftedCutSpace_common_localInverse [∀ v, Fintype (Phys v)]
    {ι : Type*} (i₀ : ι)
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (ρ v) (localSiteMap tail head D A v))
    (R : ι → Finset Vertex) (C : ι → Finset Edge)
    (hcut : ∀ i (p : Endpoint Edge), endpointVertex tail head p ∉ R i → p.1 ∈ C i)
    (hcover : ∀ v, (∃ i, v ∈ R i) ∨ LinearMap.range (localSiteMap tail head D A v) = ⊤) :
    ∃ F : (v : Vertex) → Matrix (LocalConfig tail head D v) (Phys v) ℂ,
      (∀ C M, dependentPhysicalProductFamilyMap F (cutMap tail head D A C M) =
        cutMap tail head D (representationAveragingSite tail head D ρ) C M) ∧
      ∀ ψ ∈ (⨅ i, liftedCutSpace tail head D A (R i) (C i)),
        dependentPhysicalProductFamilyMap F ψ ∈
          (⨅ i, cutSpace tail head D (representationAveragingSite tail head D ρ) (C i)) ∧
        dependentPhysicalProductFamilyMap
          (fun v ↦ LinearMap.toMatrix' (localSiteMap tail head D A v))
          (dependentPhysicalProductFamilyMap F ψ) = ψ := by
  obtain ⟨F, hF⟩ := exists_cutMap_localInverse tail head D ρ A hA
  refine ⟨F, hF, ?_⟩
  intro ψ hψ
  rw [iInf_liftedCutSpace_eq_iInf_cutSpace tail head D A R C hcut hcover] at hψ
  have hcuts i : ψ ∈ cutSpace tail head D A (C i) := (Submodule.mem_iInf _).mp hψ i
  constructor
  · apply (Submodule.mem_iInf _).mpr
    intro i
    obtain ⟨M, hM⟩ := hcuts i
    exact ⟨M, (hF (C i) M).symm.trans (congrArg (dependentPhysicalProductFamilyMap F) hM)⟩
  · obtain ⟨M, rfl⟩ := hcuts i₀
    rw [hF]
    exact cutMap_recover_representationAveragingSite tail head D ρ A
      (fun v ↦ (hA v).invariant) (C i₀) M

end TNLean.PEPS.DependentBondNetwork
