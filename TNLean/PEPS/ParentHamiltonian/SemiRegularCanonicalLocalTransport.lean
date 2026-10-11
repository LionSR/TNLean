/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.CopyCanonicalLocalTransport
import TNLean.PEPS.GraphOpenMultiplicityTransport

/-!
# Canonical regional ranges under semi-regular bond restoration

The actual open-region contraction spaces are expressed in their physical
bond coordinates. The explicit boundary transformation and its adjoint then
carry their genuine regional ranges into each other. No equality of parent
kernels or spanning of global ground vectors is assumed.

Source: SCP10, arXiv:1001.3807, Theorem 5.7 and Section 7, lines 2977–3019.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
variable {G : Type*} [Group G] [Fintype G] {p q : ℕ}

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The regional multiplicity map in numbered physical coordinates. -/
def numberedRegionMultiplicityMatrix (d : I → ℕ)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    (R : Finset V) (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i)) :
    Matrix (RegionPhysicalConfig (d := q) R) (RegionPhysicalConfig (d := p) R) ℂ :=
  numberedRegionCopyMatrix d d eX eY R γ

/-- The explicit open-generator formula gives a local-range inclusion in
bond coordinates. -/
theorem graphRegionMultiplicityMatrix_maps_openBondSpace
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (R : Finset V)
    (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i)) :
    (graphOpenBondSpace (blockMatrixRepresentation d D) (blockFourthRootWeight d) R).map
      (Matrix.mulVecLin (graphRegionMultiplicityMatrix d R γ)) ≤
      graphOpenBondSpace (multiplicityRestoredRepresentation d D) 1 R := by
  simpa only [graphRegionMultiplicityMatrix, blockMultiplicityRootWeight_self,
    blockMultiplicityRepresentation_self] using
      graphRegionCopyMatrix_maps_openBondSpace d d D hd R γ

/-- The explicit adjoint boundary formula gives the opposite local-range
inclusion, without requiring ambient physical surjectivity. -/
theorem graphRegionMultiplicityMatrix_adjoint_maps_openBondSpace
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (R : Finset V)
    (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i)) :
    (graphOpenBondSpace (multiplicityRestoredRepresentation d D) 1 R).map
      (Matrix.mulVecLin (graphRegionMultiplicityMatrix d R γ).conjTranspose) ≤
      graphOpenBondSpace (blockMatrixRepresentation d D) (blockFourthRootWeight d) R := by
  simpa only [graphRegionMultiplicityMatrix, blockMultiplicityRootWeight_self,
    blockMultiplicityRepresentation_self] using
      graphRegionCopyMatrix_adjoint_maps_openBondSpace d d D hd R γ

/-- The actual numbered regional spaces are carried forward by the explicit
regional multiplicity matrix. -/
theorem numberedRegionMultiplicityMatrix_maps_regionGroundSpace
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    (R : Finset V) (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i)) :
    (regionGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R).map
      (Matrix.mulVecLin (numberedRegionMultiplicityMatrix d eX eY R γ)) ≤
      regionGroundSpace (numberedGraphDressedAveragingTensor
        (multiplicityRestoredRepresentation d D) 1 eY) R := by
  simpa only [numberedRegionMultiplicityMatrix, blockMultiplicityRootWeight_self,
    blockMultiplicityRepresentation_self] using
      numberedRegionCopyMatrix_maps_regionGroundSpace d d D hd eX eY R γ

/-- The adjoint numbered matrix carries the actual repeated regional range
back into the actual weighted regional range. -/
theorem numberedRegionMultiplicityMatrix_adjoint_maps_regionGroundSpace
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin q)
    (R : Finset V) (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i)) :
    (regionGroundSpace (numberedGraphDressedAveragingTensor
      (multiplicityRestoredRepresentation d D) 1 eY) R).map
      (Matrix.mulVecLin (numberedRegionMultiplicityMatrix d eX eY R γ).conjTranspose) ≤
      regionGroundSpace (numberedGraphDressedAveragingTensor
        (blockMatrixRepresentation d D) (blockFourthRootWeight d) eX) R := by
  simpa only [numberedRegionMultiplicityMatrix, blockMultiplicityRootWeight_self,
    blockMultiplicityRepresentation_self] using
      numberedRegionCopyMatrix_adjoint_maps_regionGroundSpace d d D hd eX eY R γ

end TNLean.PEPS
