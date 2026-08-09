/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalSectorCompletePositivity
import TNLean.MPS.MPDO.VerticalSectorInvertibility

/-!
# Identity compositions of the transported vertical-sector maps

The transported coarse-graining and refinement maps are mutually inverse on
their vertical-sector algebras.  Each square composite is positive and trace
preserving, and its trace adjoint satisfies the Schwarz inequality.  The
composite fixes the corresponding weighted vertical bond contractions, whose
positive-length products span the sector algebra.  The fixed-point
density-block criterion therefore makes each composite the identity.

No product of fixed contractions is assumed to be fixed.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1974--1995.
-/

open scoped Matrix MatrixOrder ComplexOrder

noncomputable section

namespace MPOTensor

/-- The transported coarse-graining--refinement and
refinement--coarse-graining composites are the identities on their respective
vertical-sector algebras.

The hypotheses are precisely those of the tensor-derived trace-preservation
and trace-adjoint Schwarz theorems.  The proof uses only positivity, trace
preservation, the two Schwarz inequalities, fixedness of the distinguished
contraction families, and their positive-length product spans.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1995. -/
theorem transportedVerticalSector_composites_eq_id
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :
    h.SbarTbar = LinearMap.id ∧
      h.TbarSbar = LinearMap.id := by
  classical
  have hF₁pos := h.SbarTbar_isPositiveDirectSumMap
  have hF₂pos := h.TbarSbar_isPositiveDirectSumMap
  obtain ⟨hF₁TP, hF₂TP, _, _⟩ :=
    transportedVerticalSector_composites_tracePreserving h
  obtain ⟨hF₁Schwarz, hF₂Schwarz⟩ :=
    transportedVerticalSector_composites_traceAdjointSchwarz h
  obtain ⟨L₁, hL₁, hSpan₁⟩ :=
    exists_positive_verticalMultiplicityTraceBondContractionProductSpanTop_of_bnt
      h.hBNT₁ h.weight₁ h.hMult₁ h.hWeight₁
  obtain ⟨L₂, hL₂, hSpan₂⟩ :=
    exists_positive_verticalMultiplicityTraceBondContractionProductSpanTop_of_bnt
      h.hBNT₂ h.weight₂ h.hMult₂ h.hWeight₂
  have hFixed₁ (X : Matrix (Fin D) (Fin D) ℂ) :
      h.SbarTbar (weightedVerticalBondContraction
        (verticalMultiplicityTrace h.weight₁) h.A₁ X) =
        weightedVerticalBondContraction
          (verticalMultiplicityTrace h.weight₁) h.A₁ X := by
    change h.SbarTbar (fun α ↦ verticalMultiplicityTrace h.weight₁ α •
      MPSTensor.contractBondMatrix (h.A₁ α) X) =
        fun α ↦ verticalMultiplicityTrace h.weight₁ α •
          MPSTensor.contractBondMatrix (h.A₁ α) X
    exact transportedVerticalSectorS_comp_T_fixed_contractBondMatrix_trace_smul
      h.toVerticalSectorFixedGeneratorHypotheses X
  have hFixed₂ (X : Matrix (Fin D) (Fin D) ℂ) :
      h.TbarSbar (weightedVerticalBondContraction
        (verticalMultiplicityTrace h.weight₂) h.A₂ X) =
        weightedVerticalBondContraction
          (verticalMultiplicityTrace h.weight₂) h.A₂ X := by
    change h.TbarSbar (fun β ↦ verticalMultiplicityTrace h.weight₂ β •
      MPSTensor.contractBondMatrix (h.A₂ β) X) =
        fun β ↦ verticalMultiplicityTrace h.weight₂ β •
          MPSTensor.contractBondMatrix (h.A₂ β) X
    exact transportedVerticalSectorT_comp_S_fixed_contractBondMatrix_trace_smul
      h.toVerticalSectorFixedGeneratorHypotheses X
  constructor
  · exact eq_id_of_weightedVerticalBondContractions_fixed_of_traceAdjointSchwarz
      (verticalMultiplicityTrace h.weight₁) h.A₁ h.SbarTbar hL₁ hF₁pos hF₁TP hF₁Schwarz
      hSpan₁ hFixed₁
  · exact eq_id_of_weightedVerticalBondContractions_fixed_of_traceAdjointSchwarz
      (verticalMultiplicityTrace h.weight₂) h.A₂ h.TbarSbar hL₂ hF₂pos hF₂TP hF₂Schwarz
      hSpan₂ hFixed₂

end MPOTensor
