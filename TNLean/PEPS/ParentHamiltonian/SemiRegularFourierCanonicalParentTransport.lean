/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.GraphCoordinateCanonicalParentTransport
import TNLean.PEPS.RegularFourierMatrix

/-!
# Canonical semi-regular parents in the genuine regular basis

Multiplicity restoration followed by the virtual Fourier coordinate change
identifies the entire canonical parent ground space with the regular model.
Both transformations were proved on actual arbitrary-boundary contractions;
neither equality of regional ranges nor equality of global kernels is assumed.

Source: SCP10, arXiv:1001.3807, Theorem 5.7 and Section 7, lines 2938–3019.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G I : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [Fintype I] [DecidableEq I] {p q r : ℕ} {ι : Type*}

/-- The actual physical operation, from weighted single-copy irreducible
coordinates through repeated blocks into the genuine regular group basis. -/
def semiRegularFourierParentMap
    (d : I → ℕ) (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eR : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    (eG : (v : V) → (IncidentEdge Γ v → G) ≃ Fin r) :
    ((V → Fin p) → ℂ) →ₗ[ℂ] ((V → Fin r) → ℂ) :=
  Matrix.mulVecLin (graphNumberedBondMatrix eR eG (bondCoordinateMatrix Q)) ∘ₗ
    Matrix.mulVecLin (graphNumberedBondMatrix eX eR
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))))

/-- The full canonical parent space is mapped onto the regular parent space.
Every bond must lie inside some chosen region, exactly as required to enforce
the supported multiplicity sectors; no additional graph hypotheses are used. -/
theorem map_regionParentGroundSpace_semiRegular_fourier_eq
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hQ : Q.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eR : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    (eG : (v : V) → (IncidentEdge Γ v → G) ≃ Fin r)
    (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R).map
        (semiRegularFourierParentMap d Q eX eR eG) =
      regionParentGroundSpace
        (numberedGraphDressedAveragingTensor (leftRegularMatrix G) 1 eG) R := by
  rw [semiRegularFourierParentMap, Submodule.map_comp,
    map_regionParentGroundSpace_multiplicity_eq d D hd eX eR R hcover]
  exact map_regionParentGroundSpace_coordinates_eq Q hQ
    (multiplicityRestoredRepresentation d D) (leftRegularMatrix G) hreg eR eG R

/-- The actual weighted canonical parent and the genuine regular canonical
parent have linearly equivalent full ground spaces. -/
def canonicalSemiRegularFourierParentEquiv
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hQ : Q.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eR : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    (eG : (v : V) → (IncidentEdge Γ v → G) ≃ Fin r)
    (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphDressedAveragingTensor (leftRegularMatrix G) 1 eG) R :=
  (canonicalMultiplicityParentEquiv d D hd eX eR R hcover).trans
    (canonicalCoordinateParentEquiv Q hQ (multiplicityRestoredRepresentation d D)
      (leftRegularMatrix G) hreg eR eG R)

/-- The regular basis has exactly the same full canonical ground-space dimension. -/
theorem finrank_regionParentGroundSpace_semiRegular_fourier_eq
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hQ : Q.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eR : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    (eG : (v : V) → (IncidentEdge Γ v → G) ≃ Fin r)
    (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Module.finrank ℂ (regionParentGroundSpace
      (numberedGraphDressedAveragingTensor (leftRegularMatrix G) 1 eG) R) =
      Module.finrank ℂ (regionParentGroundSpace (numberedGraphDressedAveragingTensor
        (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R) :=
  (canonicalSemiRegularFourierParentEquiv d D hd Q hQ hreg eX eR eG R hcover).symm.finrank_eq

/-- The composed physical operation identifies every ground vector in the
full kernels of arbitrary positive canonical parent Hamiltonians. -/
theorem map_ker_regionParentHamiltonian_semiRegular_fourier_eq [Fintype ι]
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hQ : Q.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eR : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    (eG : (v : V) → (IncidentEdge Γ v → G) ≃ Fin r)
    (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := p) (R i))
      (RegionPhysicalConfig (d := p) (R i)) ℂ)
    (K : (i : ι) → Matrix (RegionPhysicalConfig (d := r) (R i))
      (RegionPhysicalConfig (d := r) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) (R i) (H i))
    (hK : ∀ i, IsRegionParentInteraction
      (numberedGraphDressedAveragingTensor (leftRegularMatrix G) 1 eG) (R i) (K i)) :
    (Matrix.mulVecLin (regionParentHamiltonian R H)).ker.map
      (semiRegularFourierParentMap d Q eX eR eG) =
      (Matrix.mulVecLin (regionParentHamiltonian R K)).ker := by
  rw [ker_regionParentHamiltonian _ R H hH, ker_regionParentHamiltonian _ R K hK]
  exact map_regionParentGroundSpace_semiRegular_fourier_eq d D hd Q hQ hreg eX eR eG R hcover

end TNLean.PEPS
