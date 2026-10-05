/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.OrientedCopyParentTransport
import TNLean.PEPS.ParentHamiltonian.OrientedCopyWeightPhysicalTransport

/-! # Positive multiplicity changes with arbitrary native edge orientation

Every map acts on genuine regional contraction ranges and the full parent
space. Source: SCP10, Definition 5.1 and Section 7.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]

/-- The canonical parent space is independent of any positive copy multiplicity,
after the explicitly constructed physical filtering and supported bond map. -/
def canonicalOrientedPositiveMultiplicityParentEquiv
    (d m : I → ℕ) (o : Edge Γ → Bool) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) {p q : ℕ}
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMatrixRepresentation d D) 1 o eX) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMultiplicityRepresentation d m D) 1 o eY) R :=
  (canonicalOrientedCopyWeightParentEquiv d m o hm D eX R).trans
    (canonicalOrientedCopyParentEquiv o d m D hm eX eY R hcover)

/-- Two arbitrary positive multiplicity families have equivalent full canonical
parent spaces. No prescribed relation between multiplicities and dimensions is assumed. -/
def canonicalOrientedMultiplicityChangeParentEquiv
    (d m n : I → ℕ) (o : Edge Γ → Bool) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) {p q r : ℕ}
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eM : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    (eN : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (n i)) ≃ Fin r)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 o eM) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMultiplicityRepresentation d n D) 1 o eN) R :=
  (canonicalOrientedPositiveMultiplicityParentEquiv d m o D hm eX eM R hcover).symm.trans
    (canonicalOrientedPositiveMultiplicityParentEquiv d n o D hn eX eN R hcover)

end TNLean.PEPS
