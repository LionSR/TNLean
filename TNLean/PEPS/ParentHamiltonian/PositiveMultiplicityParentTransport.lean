/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.CopyCanonicalParentTransport
import TNLean.PEPS.ParentHamiltonian.CopyWeightPhysicalTransport

/-!
# Canonical parent equivalence for arbitrary positive multiplicities

Removing the positive copy weights by an invertible physical filter identifies
the canonical parent space of a repeated block representation with that of its
single-copy representation. Composing this construction compares any two
positive multiplicity families. Every local space is the genuine contraction
range, and the entire parent kernel is controlled by internal edge coverage.

Source: SCP10, arXiv:1001.3807, Section 4.1 and Theorem 5.7.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]

/-- The explicit global physical filter followed by the supported copy bond map. -/
def positiveMultiplicityParentMap
    (d m : I → ℕ) (hm : ∀ i, 0 < m i) {p q : ℕ}
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q) :
    ((V → Fin p) → ℂ) →ₗ[ℂ] ((V → Fin q) → ℂ) :=
  Matrix.mulVecLin (graphNumberedBondMatrix eX eY
    (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))) ∘ₗ
      (globalPhysicalEquiv (graphCopyWeightPhysicalEquiv d m hm eX)).toLinearMap

/-- The explicit positive-multiplicity operation maps the entire genuine parent space
onto the repeated-representation parent space. -/
theorem map_regionParentGroundSpace_positiveMultiplicity_eq
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) {p q : ℕ}
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) 1 eX) R).map
        (positiveMultiplicityParentMap d m hm eX eY) =
    regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 eY) R := by
  rw [positiveMultiplicityParentMap, Submodule.map_comp,
    map_regionParentGroundSpace_copy_weight]
  exact map_regionParentGroundSpace_copy_eq d m D hm eX eY R hcover

/-- The canonical parent space is independent of any positive copy multiplicity,
after the explicitly constructed physical filtering and supported bond map. -/
def canonicalPositiveMultiplicityParentEquiv
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) {p q : ℕ}
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) 1 eX) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMultiplicityRepresentation d m D) 1 eY) R :=
  (canonicalCopyWeightParentEquiv d m hm D eX R).trans
    (canonicalCopyParentEquiv d m D hm eX eY R hcover)

/-- Two arbitrary positive multiplicity families have equivalent full canonical
parent spaces. No prescribed relation between multiplicities and dimensions is assumed. -/
def canonicalMultiplicityChangeParentEquiv
    (d m n : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) {p q r : ℕ}
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eM : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    (eN : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (n i)) ≃ Fin r)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 eM) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMultiplicityRepresentation d n D) 1 eN) R :=
  (canonicalPositiveMultiplicityParentEquiv d m D hm eX eM R hcover).symm.trans
    (canonicalPositiveMultiplicityParentEquiv d n D hn eX eN R hcover)

/-- Exact dimension independence for arbitrary positive copy multiplicities. -/
theorem finrank_regionParentGroundSpace_positiveMultiplicity_eq
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) {p q : ℕ}
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Module.finrank ℂ (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 eY) R) =
    Module.finrank ℂ (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) 1 eX) R) :=
  (canonicalPositiveMultiplicityParentEquiv d m D hm eX eY R hcover).symm.finrank_eq

/-- Arbitrary positive local interactions with the genuine contraction kernels
have their full Hamiltonian kernels transported by the explicit multiplicity map. -/
theorem map_ker_regionParentHamiltonian_positiveMultiplicity_eq
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) {p q : ℕ}
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} [Fintype ι] (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := p) (R i))
      (RegionPhysicalConfig (d := p) (R i)) ℂ)
    (K : (i : ι) → Matrix (RegionPhysicalConfig (d := q) (R i))
      (RegionPhysicalConfig (d := q) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) 1 eX) (R i) (H i))
    (hK : ∀ i, IsRegionParentInteraction (numberedGraphDressedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 eY) (R i) (K i)) :
    (Matrix.mulVecLin (regionParentHamiltonian R H)).ker.map
      (positiveMultiplicityParentMap d m hm eX eY) =
      (Matrix.mulVecLin (regionParentHamiltonian R K)).ker := by
  rw [ker_regionParentHamiltonian _ R H hH, ker_regionParentHamiltonian _ R K hK]
  exact map_regionParentGroundSpace_positiveMultiplicity_eq d m D hm eX eY R hcover

end TNLean.PEPS
