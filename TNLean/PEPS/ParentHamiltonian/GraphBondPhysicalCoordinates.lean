/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphBondRegionBlocks

/-!
# Whole-graph physical bond coordinates

The numbered product of actual bond maps is the physical product matrix
under the genuine incidence-to-bond coordinate equivalence.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X Y : Type*} [Fintype X] [Fintype Y] {p q : ℕ}

/-- Numbered global physical configurations and actual head-tail bond coordinates. -/
def graphBondConfigEquiv
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) :
    (V → Fin p) ≃ (Edge Γ → X × X) :=
  (Equiv.piCongrRight fun v => (e v).symm).trans graphSiteBondEndpointEquiv

/-- Reorder a whole numbered physical vector into its actual bond coordinates. -/
def graphBondPhysicalEquiv
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) :
    ((V → Fin p) → ℂ) ≃ₗ[ℂ] ((Edge Γ → X × X) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (graphBondConfigEquiv e).symm

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype X] in
/-- Literal coefficient formula for the whole-graph coordinate equivalence. -/
@[simp] theorem graphBondPhysicalEquiv_apply
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (ψ : (V → Fin p) → ℂ) (β : Edge Γ → X × X) :
    graphBondPhysicalEquiv e ψ β =
      ψ (fun v => e v (graphSiteBondEndpointEquiv.symm β v)) := rfl

omit [Fintype X] [Fintype Y] in
/-- The numbered bond operator is exactly the physical product matrix in
reordered coordinates. -/
theorem graphNumberedBondMatrix_eq_submatrix
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Matrix (Y × Y) (X × X) ℂ) :
    graphNumberedBondMatrix eX eY F =
      (physicalProductMatrix (Edge Γ) F).submatrix (graphBondConfigEquiv eY)
        (graphBondConfigEquiv eX) := rfl

omit [Fintype Y] in
/-- The actual global bond operator intertwines the two physical coordinate systems. -/
theorem graphBondPhysicalEquiv_mulVec
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Matrix (Y × Y) (X × X) ℂ) (ψ : (V → Fin p) → ℂ) :
    graphBondPhysicalEquiv eY (graphNumberedBondMatrix eX eY F *ᵥ ψ) =
      physicalProductMap (Edge Γ) F (graphBondPhysicalEquiv eX ψ) := by
  funext β
  change (graphNumberedBondMatrix eX eY F *ᵥ ψ) ((graphBondConfigEquiv eY).symm β) = _
  rw [graphNumberedBondMatrix_eq_submatrix, Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rfl

end TNLean.PEPS
