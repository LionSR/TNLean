/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOpenCopyTransport

/-!
# Multiplicity restoration across actual open-region boundaries

The physical map on a region is the product of full internal bond maps and
one-ended boundary filters determined by the exterior physical endpoints.
Its action and adjoint retain the actual boundary weights. Virtual boundary
coefficients, rather than an assumed equality of regional spaces, absorb the
remaining scalar factors.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019, and the genuine
regional parent construction of Theorem 5.7.
-/

noncomputable section
open scoped Matrix BigOperators Kronecker
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
variable {G : Type*} [Group G] [Fintype G]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual regional multiplicity matrix: full maps on internal bonds and
one-ended filters on crossing bonds, with their exterior coordinates fixed. -/
def graphRegionMultiplicityMatrix (d : I → ℕ) (R : Finset V)
    (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i)) :
    Matrix ((RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i)) ×
        (RI (Γ := Γ) R → (Σ i, Fin (d i) × Fin (d i)) × (Σ i, Fin (d i) × Fin (d i))))
      ((RB (Γ := Γ) R → Σ i, Fin (d i)) ×
        (RI (Γ := Γ) R → (Σ i, Fin (d i)) × (Σ i, Fin (d i)))) ℂ :=
  graphRegionCopyMatrix d d R γ

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- An internal repeated factor is pulled back to the original weighted one. -/
theorem graphOpenInternalFactor_multiplicity_adjoint
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (R : Finset V) (q : RV R → G) (e : RI (Γ := Γ) R) :
    (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))).conjTranspose *ᵥ
        graphOpenInternalFactor (multiplicityRestoredRepresentation d D) 1 R q e =
      graphOpenInternalFactor (blockMatrixRepresentation d D) (blockFourthRootWeight d) R q e := by
  simpa only [graphRegionMultiplicityMatrix, blockMultiplicityRootWeight_self,
    blockMultiplicityRepresentation_self] using graphOpenInternalFactor_copy_adjoint d d D hd R q e

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- The adjoint of a crossing filter preserves the actual weighted boundary
factor, with a scalar depending only on the virtual and exterior labels. -/
theorem graphOpenBoundaryFactor_multiplicity_adjoint
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (R : Finset V) (q : RV R → G) (e : RB (Γ := Γ) R)
    (γ θ : Σ i, Fin (d i) × Fin (d i)) :
    (multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (d i))
      (fun _ => 1) γ).conjTranspose *ᵥ
        graphOpenBoundaryFactor (multiplicityRestoredRepresentation d D) 1 R q e θ =
      (((Real.sqrt (Real.sqrt (d θ.1 : ℝ)) : ℂ)⁻¹ *
        multiplicityBondAmplitude (fun i => Fin (d i)) (fun i => Fin (d i)) θ γ) •
        graphOpenBoundaryFactor (blockMatrixRepresentation d D) (blockFourthRootWeight d)
          R q e (multiplicityEndpointBase (fun i => Fin (d i)) (fun i => Fin (d i)) θ)) := by
  simpa only [graphRegionMultiplicityMatrix, blockMultiplicityRootWeight_self,
    blockMultiplicityRepresentation_self] using
      graphOpenBoundaryFactor_copy_adjoint d d D hd R q e γ θ

/-- The adjoint regional bond transformation sends every actual repeated
open-region generator to a scalar multiple of an actual weighted generator.
The scalar is absorbed in the arbitrary virtual boundary coefficient. -/
theorem graphRegionMultiplicityMatrix_adjoint_open
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (R : Finset V)
    (γ θ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i)) :
    (graphRegionMultiplicityMatrix d R γ).conjTranspose *ᵥ
        graphOpenBondCoordinates (multiplicityRestoredRepresentation d D) 1 R θ =
      (∏ e : RB (Γ := Γ) R, (Real.sqrt (Real.sqrt (d (θ e).1 : ℝ)) : ℂ)⁻¹ *
        multiplicityBondAmplitude (fun i => Fin (d i)) (fun i => Fin (d i)) (θ e) (γ e)) •
      graphOpenBondCoordinates (blockMatrixRepresentation d D) (blockFourthRootWeight d) R
        (fun e => multiplicityEndpointBase (fun i => Fin (d i)) (fun i => Fin (d i)) (θ e)) := by
  simpa only [graphRegionMultiplicityMatrix, blockMultiplicityRootWeight_self,
    blockMultiplicityRepresentation_self] using graphRegionCopyMatrix_adjoint_open d d D hd R γ θ

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Multiplicity restoration carries the actual weighted internal factor to
the actual repeated representation factor. -/
theorem graphOpenInternalFactor_multiplicity
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (R : Finset V) (q : RV R → G) (e : RI (Γ := Γ) R) :
    fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)) *ᵥ
        graphOpenInternalFactor (blockMatrixRepresentation d D) (blockFourthRootWeight d) R q e =
      graphOpenInternalFactor (multiplicityRestoredRepresentation d D) 1 R q e := by
  simpa only [graphRegionMultiplicityMatrix, blockMultiplicityRootWeight_self,
    blockMultiplicityRepresentation_self] using graphOpenInternalFactor_copy d d D hd R q e

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Each crossing filter sends the weighted one-ended physical factor to
an explicit linear combination of repeated virtual boundary factors. -/
theorem graphOpenBoundaryFactor_multiplicity
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (R : Finset V) (q : RV R → G) (e : RB (Γ := Γ) R)
    (γ : Σ i, Fin (d i) × Fin (d i)) (θ : Σ i, Fin (d i)) :
    multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (d i)) (fun _ => 1) γ *ᵥ
        graphOpenBoundaryFactor (blockMatrixRepresentation d D) (blockFourthRootWeight d) R q e θ =
      fun y => ∑ a : Σ i, Fin (d i) × Fin (d i),
        multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (d i))
          (fun i => (Real.sqrt (Real.sqrt (d i : ℝ)) : ℂ)) γ a θ *
        graphOpenBoundaryFactor (multiplicityRestoredRepresentation d D) 1 R q e a y := by
  simpa only [graphRegionMultiplicityMatrix, blockMultiplicityRootWeight_self,
    blockMultiplicityRepresentation_self] using graphOpenBoundaryFactor_copy d d D R q e γ θ

/-- The actual regional bond map sends a weighted open-region generator to
an explicit superposition of actual repeated open-region generators. All
crossing weights are retained in the transformed virtual boundary coefficients. -/
theorem graphRegionMultiplicityMatrix_open
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (R : Finset V)
    (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i))
    (θ : RB (Γ := Γ) R → Σ i, Fin (d i)) :
    graphRegionMultiplicityMatrix d R γ *ᵥ
        graphOpenBondCoordinates (blockMatrixRepresentation d D) (blockFourthRootWeight d) R θ =
      ∑ a : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i),
        (∏ e : RB (Γ := Γ) R,
          multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (d i))
            (fun i => (Real.sqrt (Real.sqrt (d i : ℝ)) : ℂ)) (γ e) (a e) (θ e)) •
        graphOpenBondCoordinates (multiplicityRestoredRepresentation d D) 1 R a := by
  simpa only [graphRegionMultiplicityMatrix, blockMultiplicityRootWeight_self,
    blockMultiplicityRepresentation_self] using graphRegionCopyMatrix_open d d D hd R γ θ

end TNLean.PEPS
