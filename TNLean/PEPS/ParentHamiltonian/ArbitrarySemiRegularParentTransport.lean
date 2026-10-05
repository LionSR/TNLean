/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.PositiveMultiplicityParentTransport
import TNLean.PEPS.ParentHamiltonian.GraphCoordinateCanonicalParentTransport
import TNLean.PEPS.SemiRegularMatrixBlocks
import TNLean.PEPS.SemiRegularRegularComparison

/-!
# Arbitrary unitary semi-regular canonical parent spaces

The representation decomposition is derived from the original matrices.
Its actual positive multiplicities are removed by supported bond maps and
invertible physical copy filters. The same irreducible family, with dimension
multiplicities restored, is identified with the genuine regular representation
by a derived normalized Fourier matrix. Thus this result identifies the whole
canonical parent space for arbitrary semi-regular multiplicities.

A constant incidence count supplies finite numbered physical spaces at all
intermediate stages. The region family must cover each edge internally.
Neither a local-range comparison nor a parent-kernel identity is assumed.

Source: SCP10, arXiv:1001.3807, Definition 4.5, Theorem 5.7, and Section 7.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A constant incidence count provides a common physical alphabet for any
finite virtual alphabet. -/
def countedIncidentEnumeration (X : Type*) [Fintype X] (k : ℕ)
    (hk : ∀ v : V, Fintype.card (IncidentEdge Γ v) = k) (v : V) :
    (IncidentEdge Γ v → X) ≃ Fin (Fintype.card X ^ k) :=
  (Fintype.equivFin _).trans (finCongr (by rw [Fintype.card_fun, hk v]))

variable {G X : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [Fintype X] [DecidableEq X]

/-- Every unitary semi-regular canonical tensor has the same full parent space
as the regular canonical tensor, up to a constructed linear equivalence.
The actual multiplicities and all representation coordinates are derived. -/
theorem nonempty_canonicalSemiRegularParentEquiv
    (U : G →* Matrix X X ℂ) (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (k : ℕ) (hk : ∀ v : V, Fintype.card (IncidentEdge Γ v) = k) {p : ℕ}
    (eU : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Nonempty (regionParentGroundSpace (numberedGraphDressedAveragingTensor U 1 eU) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphDressedAveragingTensor (leftRegularMatrix G) 1
        (countedIncidentEnumeration G k hk)) R) := by
  classical
  obtain ⟨K, d, m, D, Q, hd, hm, hD, hirr, hcross, hQ, hQU, _, _, hmin⟩ :=
    exists_minimalSemiRegular_matrix U hU hSemi
  obtain ⟨F, hF, _, hFL⟩ :=
    exists_isometry_multiplicityRestored_leftRegular d D hD hirr hcross hmin
  let eX := countedIncidentEnumeration (Σ i, Fin (d i)) k hk
  let eM := countedIncidentEnumeration (Σ i, Fin (d i) × Fin (m i)) k hk
  let eD := countedIncidentEnumeration (Σ i, Fin (d i) × Fin (d i)) k hk
  let E₁ := canonicalCoordinateParentEquiv Q hQ
    (blockMultiplicityRepresentation d m D) U hQU eM eU R
  let E₂ := canonicalMultiplicityChangeParentEquiv d m d D hm hd eX eM eD R hcover
  let E₃ := canonicalCoordinateParentEquiv F hF
    (multiplicityRestoredRepresentation d D) (leftRegularMatrix G) hFL eD
    (countedIncidentEnumeration G k hk) R
  exact ⟨E₁.symm.trans (E₂.trans E₃)⟩

/-- The full canonical parent-space dimension is independent of the original
unitary semi-regular representation and of all its positive multiplicities. -/
theorem finrank_regionParentGroundSpace_arbitrarySemiRegular_eq
    (U : G →* Matrix X X ℂ) (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (k : ℕ) (hk : ∀ v : V, Fintype.card (IncidentEdge Γ v) = k) {p : ℕ}
    (eU : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Module.finrank ℂ (regionParentGroundSpace
      (numberedGraphDressedAveragingTensor U 1 eU) R) =
    Module.finrank ℂ (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (leftRegularMatrix G) 1 (countedIncidentEnumeration G k hk)) R) :=
  (nonempty_canonicalSemiRegularParentEquiv U hU hSemi k hk eU R hcover).some.finrank_eq

/-- Positive local interactions with the genuine regional kernels have equivalent
full Hamiltonian kernels for an arbitrary unitary semi-regular representation. -/
theorem nonempty_ker_regionParentHamiltonian_arbitrarySemiRegular_equiv
    (U : G →* Matrix X X ℂ) (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (k : ℕ) (hk : ∀ v : V, Fintype.card (IncidentEdge Γ v) = k) {p : ℕ}
    (eU : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    {ι : Type*} [Fintype ι] (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := p) (R i))
      (RegionPhysicalConfig (d := p) (R i)) ℂ)
    (K : (i : ι) → Matrix (RegionPhysicalConfig (d := Fintype.card G ^ k) (R i))
      (RegionPhysicalConfig (d := Fintype.card G ^ k) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction
      (numberedGraphDressedAveragingTensor U 1 eU) (R i) (H i))
    (hK : ∀ i, IsRegionParentInteraction (numberedGraphDressedAveragingTensor
      (leftRegularMatrix G) 1 (countedIncidentEnumeration G k hk)) (R i) (K i)) :
    Nonempty ((Matrix.mulVecLin (regionParentHamiltonian R H)).ker ≃ₗ[ℂ]
      (Matrix.mulVecLin (regionParentHamiltonian R K)).ker) := by
  rw [ker_regionParentHamiltonian _ R H hH, ker_regionParentHamiltonian _ R K hK]
  exact nonempty_canonicalSemiRegularParentEquiv U hU hSemi k hk eU R hcover

end TNLean.PEPS
