/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.ArbitrarySemiRegularParentTransport
import TNLean.PEPS.ParentHamiltonian.GInjectiveParentTransport
import TNLean.PEPS.GraphAveragingGInjective

/-!
# Arbitrary semi-regular G-injective physical tensors

For the actual oriented incident action, the canonical averaging tensor is
G-injective. The fixed-representation physical comparison therefore identifies
any G-injective tensor with that canonical tensor, including rectangular
physical spaces. The arbitrary-multiplicity canonical comparison then reaches
the genuine regular canonical parent space.

The hypotheses are local G-injectivity, unitarity and semi-regularity of the
virtual representation, constant incidence count, and vertex/edge region
coverage. No assumed parent-space comparison is used.

Source: SCP10, arXiv:1001.3807, Definition 5.1 and Theorems 5.7 and 5.9.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G X : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [Fintype X] [DecidableEq X]

omit [DecidableEq G] in
/-- Any G-injective physical tensor for the actual oriented incident action has
its whole parent space equivalent to the canonical averaging parent space. -/
theorem nonempty_gInjectiveCanonicalParentEquiv
    (U : G →* Matrix X X ℂ) {p q : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → X) → Fin p → ℂ)
    (ha : ∀ v, IsGInjective (graphNumberedIncidentRepresentation U v)
      (localTensorMap (groupBondTensor a) v))
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    Nonempty (regionParentGroundSpace (groupBondTensor a) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphDressedAveragingTensor U 1 e) R) := by
  let A := numberedGraphDressedAveragingTensor U 1 e
  obtain ⟨F, hF, hinj⟩ := exists_physicalDeform_eq_of_isGInjective A
    (groupBondTensor a).component (graphNumberedIncidentRepresentation U)
    (isGInjective_numberedGraphDressedAveragingTensor_one U e) ha
  have E := regionParentGroundSpaceRangeEquiv A F hinj R hcover
  have heq : physicalDeform A F = groupBondTensor a := hF
  rw [heq] at E
  exact ⟨E.symm⟩

/-- Full parent-space equivalence for an arbitrary semi-regular G-injective
physical tensor, with the representation blocks and their multiplicities derived. -/
theorem nonempty_semiRegularGInjectiveParentEquiv
    (U : G →* Matrix X X ℂ) (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    {p : ℕ} (a : (v : V) → (IncidentEdge Γ v → X) → Fin p → ℂ)
    (ha : ∀ v, IsGInjective (graphNumberedIncidentRepresentation U v)
      (localTensorMap (groupBondTensor a) v))
    (k : ℕ) (hk : ∀ v : V, Fintype.card (IncidentEdge Γ v) = k)
    {ι : Type*} (R : ι → Finset V)
    (hv : ∀ v, ∃ i, v ∈ R i)
    (he : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Nonempty (regionParentGroundSpace (groupBondTensor a) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphDressedAveragingTensor (leftRegularMatrix G) 1
        (countedIncidentEnumeration G k hk)) R) := by
  obtain ⟨E₁⟩ := nonempty_gInjectiveCanonicalParentEquiv U a ha
    (countedIncidentEnumeration X k hk) R hv
  obtain ⟨E₂⟩ := nonempty_canonicalSemiRegularParentEquiv U hU hSemi k hk
    (countedIncidentEnumeration X k hk) R he
  exact ⟨E₁.trans E₂⟩

/-- The full parent ground-space dimension for arbitrary physical tensors is
independent of their unitary semi-regular virtual representation. -/
theorem finrank_regionParentGroundSpace_semiRegularGInjective_eq
    (U : G →* Matrix X X ℂ) (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    {p : ℕ} (a : (v : V) → (IncidentEdge Γ v → X) → Fin p → ℂ)
    (ha : ∀ v, IsGInjective (graphNumberedIncidentRepresentation U v)
      (localTensorMap (groupBondTensor a) v))
    (k : ℕ) (hk : ∀ v : V, Fintype.card (IncidentEdge Γ v) = k)
    {ι : Type*} (R : ι → Finset V)
    (hv : ∀ v, ∃ i, v ∈ R i)
    (he : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    Module.finrank ℂ (regionParentGroundSpace (groupBondTensor a) R) =
    Module.finrank ℂ (regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (leftRegularMatrix G) 1 (countedIncidentEnumeration G k hk)) R) :=
  (nonempty_semiRegularGInjectiveParentEquiv U hU hSemi a ha k hk R hv he).some.finrank_eq

/-- The complete Hamiltonian kernels of arbitrary positive canonical local
parents are equivalent for every semi-regular G-injective physical tensor. -/
theorem nonempty_ker_regionParentHamiltonian_semiRegularGInjective_equiv
    (U : G →* Matrix X X ℂ) (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    {p : ℕ} (a : (v : V) → (IncidentEdge Γ v → X) → Fin p → ℂ)
    (ha : ∀ v, IsGInjective (graphNumberedIncidentRepresentation U v)
      (localTensorMap (groupBondTensor a) v))
    (k : ℕ) (hk : ∀ v : V, Fintype.card (IncidentEdge Γ v) = k)
    {ι : Type*} [Fintype ι] (R : ι → Finset V)
    (hv : ∀ v, ∃ i, v ∈ R i)
    (he : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := p) (R i))
      (RegionPhysicalConfig (d := p) (R i)) ℂ)
    (K : (i : ι) → Matrix (RegionPhysicalConfig (d := Fintype.card G ^ k) (R i))
      (RegionPhysicalConfig (d := Fintype.card G ^ k) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction (groupBondTensor a) (R i) (H i))
    (hK : ∀ i, IsRegionParentInteraction (numberedGraphDressedAveragingTensor
      (leftRegularMatrix G) 1 (countedIncidentEnumeration G k hk)) (R i) (K i)) :
    Nonempty ((Matrix.mulVecLin (regionParentHamiltonian R H)).ker ≃ₗ[ℂ]
      (Matrix.mulVecLin (regionParentHamiltonian R K)).ker) := by
  rw [ker_regionParentHamiltonian _ R H hH, ker_regionParentHamiltonian _ R K hK]
  exact nonempty_semiRegularGInjectiveParentEquiv U hU hSemi a ha k hk R hv he

end TNLean.PEPS
