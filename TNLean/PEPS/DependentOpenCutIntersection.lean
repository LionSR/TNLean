/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentOpenBondSupport
import TNLean.PEPS.DependentPartialAverageSupport
import TNLean.PEPS.DependentBondLocalInverse

/-!
# Open cut intersections when the internal labels can be removed

Internal representation support follows from the actual cut ranges. A coherent
expansion retains arbitrary matrices on the exterior bonds, and the product of
local averages sends each term to a network. If vertex symmetries remove all
internal group labels, that network is in the minimal open cut range.
For a three-core path the required vertex labels are given explicitly.

Source: SCP10, arXiv:1001.3807, Theorem 5.4.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge G : Type*} [Group G] [Fintype G]
variable [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] [DecidableEq Edge]
variable (tail head : Edge → Vertex) (D : Edge → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : Vertex → Type*}

omit [DecidableEq Vertex] in
/-- A network whose internal bonds are identities is an actual open cut vector. -/
theorem network_mem_cutSpace_of_eq_one
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (C : Finset Edge) (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (hB : ∀ e, e ∉ C → B e = 1) :
    network tail head D A B ∈ cutSpace tail head D A C := by
  refine ⟨cutBondBoundary D C B, ?_⟩
  funext σ
  rw [cutMap_apply, cutCoeff_bondBoundary]
  congr 1
  funext e
  by_cases he : e ∈ C <;> simp [he, hB e]

omit [DecidableEq Vertex] in
/-- Cutting additional bonds can only enlarge the actual correlated-boundary range. -/
theorem cutSpace_mono
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    {C C' : Finset Edge} (hC : C ⊆ C') :
    cutSpace tail head D A C ≤ cutSpace tail head D A C' := by
  classical
  rw [cutSpace_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨η, rfl⟩
  change cutMap tail head D A C (Pi.single η 1) ∈ _
  rw [funext (cutMap_single_eq_network tail head D A C η)]
  apply network_mem_cutSpace_of_eq_one
  intro e he
  have he' : e ∉ C := fun h ↦ he (hC h)
  simp [cutBondUnits, he']

/-- Physical maps carry the whole cut range to the corresponding deformed range. -/
theorem map_cutSpace {Out : Vertex → Type*} [∀ v, Fintype (Phys v)]
    (F : (v : Vertex) → Matrix (Out v) (Phys v) ℂ)
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ) (C : Finset Edge) :
    (cutSpace tail head D A C).map (dependentPhysicalProductFamilyMap F) =
      cutSpace tail head D (physicalMapSite tail head D F A) C := by
  change (cutMap tail head D A C).range.map _ = _
  rw [← LinearMap.range_comp]
  congr 1
  apply LinearMap.ext
  intro M
  exact physicalMap_cutMap tail head D F A C M

/-- Applying all selected local averages to a bare matrix product gives the
actual partially averaged network with those same bond matrices. -/
theorem averagingProjector_matrixBondProduct
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) :
    averagingProjector tail head D ρ (matrixBondProduct tail head D B) =
      network tail head D (representationAveragingSite tail head D ρ) B := by
  have hbare : matrixBondProduct tail head D B =
      network tail head D (identitySite tail head D) B := by
    funext σ
    rw [network_identitySite]
    rfl
  rw [hbare, averagingProjector_network_identitySite]

/-- Removing the internal group labels moves every projected spanning vector
into the range with all exterior bonds left open. -/
theorem averagingProjector_openBondProduct_mem_cutSpace
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ) (f : Vertex → G →* G)
    (C : Finset Edge)
    (hremove : ∀ p : Edge → G, ∃ q : Vertex → G, ∀ e, e ∉ C →
      f (head e) (q (head e)) * p e * (f (tail e) (q (tail e)))⁻¹ = 1)
    (p : (e : Edge) → OpenBondLabel (G := G) D e) :
    averagingProjector tail head D (partialIncidentRepresentation tail head D U f)
        (matrixBondProduct tail head D (fun e ↦ openBondGenerator D U C e (p e))) ∈
      cutSpace tail head D (partialAveragingSite tail head D U f) C := by
  obtain ⟨q, hq⟩ := hremove (fun e ↦ (p e).elim id (fun _ ↦ 1))
  rw [averagingProjector_matrixBondProduct]
  change network tail head D (partialAveragingSite tail head D U f) _ ∈ _
  rw [← funext (network_partialAveragingSite_bondGauge tail head D U f
    (fun e ↦ openBondGenerator D U C e (p e)) q)]
  apply network_mem_cutSpace_of_eq_one
  intro e he
  simp only [gaugeBondMatrix, openBondGenerator, he, ↓reduceIte, ← map_mul, hq e he, map_one]

/-- Actual canonical cut memberships force the minimal open cut range whenever
all internal group labels can be removed by the selected vertex symmetries. -/
theorem iInf_partialCutSpace_eq_of_remove_labels
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ) (f : Vertex → G →* G)
    (C₀ : Finset Edge) {ι : Type*} (i₀ : ι) (C : ι → Finset Edge)
    (hsub : ∀ i, C₀ ⊆ C i) (hcover : ∀ e, e ∉ C₀ → ∃ i, e ∉ C i)
    (hremove : ∀ p : Edge → G, ∃ q : Vertex → G, ∀ e, e ∉ C₀ →
      f (head e) (q (head e)) * p e * (f (tail e) (q (tail e)))⁻¹ = 1) :
    (⨅ i, cutSpace tail head D (partialAveragingSite tail head D U f) (C i)) =
      cutSpace tail head D (partialAveragingSite tail head D U f) C₀ := by
  classical
  apply le_antisymm
  · intro ψ hψ
    have hcuts i : ψ ∈ cutSpace tail head D (partialAveragingSite tail head D U f) (C i) :=
      (Submodule.mem_iInf _).mp hψ i
    obtain ⟨c, hc⟩ := exists_openBondCoefficients_of_slices tail head D U C₀ (ψ := ψ) (by
      intro e he τ
      obtain ⟨i, hi⟩ := hcover e he
      exact physicalBondSlice_mem_range_of_mem_partialCutSpace tail head D U f
        (C i) e hi τ (hcuts i))
    have hfixed : averagingProjector tail head D
        (partialIncidentRepresentation tail head D U f) ψ = ψ := by
      obtain ⟨M, rfl⟩ := hcuts i₀
      exact averagingProjector_cutMap tail head D _ (C i₀) M
    rw [← hfixed, hc, map_sum]
    simp_rw [map_smul]
    exact Submodule.sum_smul_mem _ _ fun p _ ↦
      averagingProjector_openBondProduct_mem_cutSpace tail head D U f C₀ hremove p
  · exact le_iInf fun i ↦ cutSpace_mono tail head D _ (hsub i)

omit [Fintype G] in
/-- One genuine local inverse transports the complete open intersection from
canonical averages to arbitrary invariant physical tensors. -/
theorem iInf_cutSpace_eq_of_remove_labels [Finite G] [∀ v, Finite (Phys v)]
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ) (f : Vertex → G →* G)
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (partialIncidentRepresentation tail head D U f v)
      (localSiteMap tail head D A v))
    (C₀ : Finset Edge) {ι : Type*} (i₀ : ι) (C : ι → Finset Edge)
    (hsub : ∀ i, C₀ ⊆ C i) (hcover : ∀ e, e ∉ C₀ → ∃ i, e ∉ C i)
    (hremove : ∀ p : Edge → G, ∃ q : Vertex → G, ∀ e, e ∉ C₀ →
      f (head e) (q (head e)) * p e * (f (tail e) (q (tail e)))⁻¹ = 1) :
    (⨅ i, cutSpace tail head D A (C i)) = cutSpace tail head D A C₀ := by
  let := Fintype.ofFinite G
  rw [iInf_cutSpace_eq_map_representationAveragingSite tail head D i₀ _ A hA C]
  change (⨅ i, cutSpace tail head D (partialAveragingSite tail head D U f) (C i)).map _ = _
  rw [iInf_partialCutSpace_eq_of_remove_labels tail head D U f C₀ i₀ C hsub hcover hremove,
    map_cutSpace]
  congr 1
  exact physicalMap_recover_representationAveragingSite tail head D _ A
    (fun v ↦ (hA v).invariant)

end TNLean.PEPS.DependentBondNetwork
