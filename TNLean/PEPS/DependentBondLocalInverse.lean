/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondCut
import TNLean.PEPS.DependentBondProjectorExpansion
import TNLean.PEPS.DependentPhysicalProductRangeSupport

/-!
# Local inverses with dependent virtual and physical dimensions

A product of genuine local G-injective inverses transports every actual cut
contraction to its canonical averaging counterpart with the entire original
joint boundary retained. The same inverse works simultaneously on any
nonempty family of cuts. Both the virtual edge alphabets and the physical
site alphabets may vary.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge : Type*} [Fintype Vertex] [Fintype Edge]
variable [DecidableEq Vertex] [DecidableEq Edge]
variable (tail head : Edge → Vertex) (D : Edge → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys Out : Vertex → Type*}

/-- Apply an independently sized matrix to the physical index of each tensor. -/
def physicalMapSite [∀ v, Fintype (Phys v)]
    (F : (v : Vertex) → Matrix (Out v) (Phys v) ℂ)
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (v : Vertex) (η : LocalConfig tail head D v) (s : Out v) : ℂ :=
  ∑ t, F v s t * A v η t

omit [Fintype Vertex] [∀ e, DecidableEq (D e)] in
/-- Physical coefficient maps compose with the actual local site maps. -/
theorem localSiteMap_physicalMapSite [∀ v, Fintype (Phys v)]
    (F : (v : Vertex) → Matrix (Out v) (Phys v) ℂ)
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ) (v : Vertex) :
    localSiteMap tail head D (physicalMapSite tail head D F A) v =
      Matrix.mulVecLin (F v) ∘ₗ localSiteMap tail head D A v := by
  exact Matrix.mulVecLin_mul (F v) (fun s η ↦ A v η s)

omit [Fintype Vertex] [∀ e, DecidableEq (D e)] in
/-- Local site maps determine every coefficient of the original tensor family. -/
theorem localSiteMap_family_injective
    (A B : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (h : ∀ v, localSiteMap tail head D A v = localSiteMap tail head D B v) : A = B := by
  classical
  funext v η s
  have hv := congrFun (LinearMap.congr_fun (h v) (Pi.single η 1)) s
  simpa [localSiteMap_apply, Pi.single_apply] using hv

/-- Products of physical maps commute with arbitrary correlated cut contractions. -/
theorem physicalMap_cutMap [∀ v, Fintype (Phys v)]
    (F : (v : Vertex) → Matrix (Out v) (Phys v) ℂ)
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (C : Finset Edge) (M : CutConfig C D → ℂ) :
    dependentPhysicalProductFamilyMap F (cutMap tail head D A C M) =
      cutMap tail head D (physicalMapSite tail head D F A) C M := by
  funext τ
  simp only [dependentPhysicalProductFamilyMap_apply, cutMap_apply, cutCoeff,
    physicalMapSite, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp only [Finset.prod_mul_distrib]
  ring

omit [∀ e, DecidableEq (D e)] in
/-- Physical maps also commute with the uncut network with arbitrary bond matrices. -/
theorem physicalMap_network [∀ v, Fintype (Phys v)]
    (F : (v : Vertex) → Matrix (Out v) (Phys v) ℂ)
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) :
    dependentPhysicalProductFamilyMap F (network tail head D A B) =
      network tail head D (physicalMapSite tail head D F A) B := by
  funext τ
  simp only [dependentPhysicalProductFamilyMap_apply, network, physicalMapSite, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp only [Finset.prod_mul_distrib]
  ring

variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] Representation.invertibleFintypeCardComplex

omit [Fintype Vertex] in
/-- Independent local G-injective inverses send the original coefficients to
the canonical projector coefficients, without a uniform dimension assumption. -/
theorem exists_physicalMap_to_representationAveragingSite [∀ v, Fintype (Phys v)]
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (ρ v) (localSiteMap tail head D A v)) :
    ∃ F : (v : Vertex) → Matrix (LocalConfig tail head D v) (Phys v) ℂ,
      physicalMapSite tail head D F A = representationAveragingSite tail head D ρ := by
  classical
  have hlocal v := ((isGInjective_iff_exists_leftInverse _ _).mp (hA v)).2
  choose L hL using hlocal
  refine ⟨fun v ↦ LinearMap.toMatrix' (L v), ?_⟩
  apply localSiteMap_family_injective tail head D
  intro v
  rw [localSiteMap_physicalMapSite, localSiteMap_representationAveragingSite]
  change Matrix.toLin' (LinearMap.toMatrix' (L v)) ∘ₗ _ = _
  rw [Matrix.toLin'_toMatrix', hL]

omit [Fintype Vertex] in
/-- The original invariant tensors recover their coefficients from the local
projectors, with their own physical dimensions retained. -/
theorem physicalMap_recover_representationAveragingSite
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (hA : ∀ v g, localSiteMap tail head D A v ∘ₗ ρ v g = localSiteMap tail head D A v) :
    physicalMapSite tail head D (fun v ↦ LinearMap.toMatrix' (localSiteMap tail head D A v))
        (representationAveragingSite tail head D ρ) = A := by
  apply localSiteMap_family_injective tail head D
  intro v
  rw [localSiteMap_physicalMapSite, localSiteMap_representationAveragingSite]
  change Matrix.toLin' (LinearMap.toMatrix' (localSiteMap tail head D A v)) ∘ₗ _ = _
  rw [Matrix.toLin'_toMatrix']
  exact LinearMap.ext (apply_averageMap_of_forall_comp_eq (hA v))

/-- One product of local inverses transports every cut with exactly the same boundary. -/
theorem exists_cutMap_localInverse [∀ v, Fintype (Phys v)]
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (ρ v) (localSiteMap tail head D A v)) :
    ∃ F : (v : Vertex) → Matrix (LocalConfig tail head D v) (Phys v) ℂ,
      ∀ C M, dependentPhysicalProductFamilyMap F (cutMap tail head D A C M) =
        cutMap tail head D (representationAveragingSite tail head D ρ) C M := by
  obtain ⟨F, hF⟩ := exists_physicalMap_to_representationAveragingSite tail head D ρ A hA
  refine ⟨F, fun C M ↦ ?_⟩
  rw [physicalMap_cutMap, hF]

/-- The original site maps recover every actual cut vector from its canonical image. -/
theorem cutMap_recover_representationAveragingSite
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (hA : ∀ v g, localSiteMap tail head D A v ∘ₗ ρ v g = localSiteMap tail head D A v)
    (C : Finset Edge) (M : CutConfig C D → ℂ) :
    dependentPhysicalProductFamilyMap
        (fun v ↦ LinearMap.toMatrix' (localSiteMap tail head D A v))
        (cutMap tail head D (representationAveragingSite tail head D ρ) C M) =
      cutMap tail head D A C M := by
  rw [physicalMap_cutMap, physicalMap_recover_representationAveragingSite tail head D ρ A hA]

/-- A nonempty family of genuine cut spaces is transported by one common local
inverse, so its intersection is exactly the image of its canonical intersection. -/
theorem iInf_cutSpace_eq_map_representationAveragingSite
    {ι : Type*} (i₀ : ι) [∀ v, Finite (Phys v)]
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (ρ v) (localSiteMap tail head D A v))
    (C : ι → Finset Edge) :
    (⨅ i, cutSpace tail head D A (C i)) =
      (⨅ i, cutSpace tail head D (representationAveragingSite tail head D ρ) (C i)).map
        (dependentPhysicalProductFamilyMap
          (fun v ↦ LinearMap.toMatrix' (localSiteMap tail head D A v))) := by
  classical
  let (v : Vertex) := Fintype.ofFinite (Phys v)
  obtain ⟨F, hF⟩ := exists_cutMap_localInverse tail head D ρ A hA
  have hR := cutMap_recover_representationAveragingSite tail head D ρ A
    (fun v ↦ (hA v).invariant)
  apply le_antisymm
  · intro ψ hψ
    have hcuts i : ψ ∈ cutSpace tail head D A (C i) := ((Submodule.mem_iInf _).mp hψ) i
    refine ⟨dependentPhysicalProductFamilyMap F ψ, ?_, ?_⟩
    · apply (Submodule.mem_iInf _).mpr
      intro i
      obtain ⟨M, hM⟩ := hcuts i
      exact ⟨M, (hF (C i) M).symm.trans (congrArg (dependentPhysicalProductFamilyMap F) hM)⟩
    · obtain ⟨M, hM⟩ := hcuts i₀
      rw [← hM, hF, hR]
  · rintro _ ⟨χ, hχ, rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro i
    obtain ⟨M, hM⟩ := ((Submodule.mem_iInf _).mp hχ) i
    exact ⟨M, (hR (C i) M).symm.trans (congrArg
      (dependentPhysicalProductFamilyMap
        (fun v ↦ LinearMap.toMatrix' (localSiteMap tail head D A v))) hM)⟩

/-- The identity tensor exposes every local virtual configuration as a physical one. -/
def identitySite (v : Vertex) (η s : LocalConfig tail head D v) : ℂ :=
  if η = s then 1 else 0

/-- Identity sites leave precisely the product of the actual bond entries. -/
theorem network_identitySite
    (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (σ : (v : Vertex) → LocalConfig tail head D v) :
    network tail head D (identitySite tail head D) B σ =
      bondWeight D B ((endpointSiteEquiv tail head D).symm σ) := by
  classical
  rw [network_eq_sum_site]
  simp [identitySite, Fintype.prod_boole, ← funext_iff]

/-- The product of the actual local averaging projections. -/
def averagingProjector
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ)) :
    (((v : Vertex) → LocalConfig tail head D v) → ℂ) →ₗ[ℂ]
      (((v : Vertex) → LocalConfig tail head D v) → ℂ) :=
  dependentPhysicalProductFamilyMap (fun v ↦
    LinearMap.toMatrix' (localSiteMap tail head D (representationAveragingSite tail head D ρ) v))

/-- Every canonical cut vector is fixed by the product local projection. -/
theorem averagingProjector_cutMap
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (C : Finset Edge) (M : CutConfig C D → ℂ) :
    averagingProjector tail head D ρ
        (cutMap tail head D (representationAveragingSite tail head D ρ) C M) =
      cutMap tail head D (representationAveragingSite tail head D ρ) C M :=
  cutMap_recover_representationAveragingSite tail head D ρ _
    (fun v ↦ (isGInjective_representationAveragingSite tail head D ρ v).invariant) C M

/-- Projecting the bare identity-site bond product produces the actual canonical network. -/
theorem averagingProjector_network_identitySite
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) :
    averagingProjector tail head D ρ (network tail head D (identitySite tail head D) B) =
      network tail head D (representationAveragingSite tail head D ρ) B := by
  classical
  have hid : physicalMapSite tail head D (fun v ↦
      LinearMap.toMatrix' (localSiteMap tail head D (representationAveragingSite tail head D ρ) v))
      (identitySite tail head D) = representationAveragingSite tail head D ρ := by
    funext v η s
    simp [physicalMapSite, identitySite, representationAveragingSite]
  rw [averagingProjector, physicalMap_network, hid]

end TNLean.PEPS.DependentBondNetwork
