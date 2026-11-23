/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.FixedPoint.DirectSum.TraceNonincreasingDirectSum
import TNLean.MPS.MPDO.SectorMaps.VerticalSectorDensityBlocks
import TNLean.MPS.MPDO.SectorMaps.VerticalSectorGeneration
import TNLean.MPS.MPDO.SectorMaps.VerticalSectorCompletePositivity
import QICLean.Channel.FixedPoint.DirectSum.DirectSumBlockPermutation

/-!
# Identity criterion for vertical-sector maps

A positive trace-preserving endomorphism of a finite product of matrix
algebras has a positive-definite fixed family when fixed factors generate the
identity by products of one positive length.  If its trace adjoint satisfies
the Schwarz inequality, the density-block description of its fixed points
then shows that the endomorphism is the identity.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1980--1995.
* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.14 and
  Equation (6.63).

## Identity compositions of the transported vertical-sector maps

The transported coarse-graining and refinement maps are mutually inverse on
their vertical-sector algebras.  Each square composite is positive and trace
preserving, and its trace adjoint satisfies the Schwarz inequality.  The
composite fixes the corresponding weighted vertical bond contractions, whose
positive-length products span the sector algebra.  The fixed-point
density-block criterion therefore makes each composite the identity.

No product of fixed contractions is assumed to be fixed.

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1974--1995.

## Relabelling of transported vertical sectors

The mutually inverse transported vertical-sector maps determine the same
matching of simple matrix summands as their trace-adjoint star-algebra
equivalence.  This file specializes the abstract classification to the
vertical canonical forms of an MPDO.

The source is CPSV16, arXiv:1606.00608, Appendix C.4, line 1997.  The
multiplicity and coefficient calculation at lines 2001--2008 is not used.
-/

section

open scoped Matrix MatrixOrder ComplexOrder

noncomputable section

namespace MPOTensor

/-- A positive trace-preserving endomorphism of a vertical-sector algebra is
the identity if its trace adjoint satisfies the Schwarz inequality and it
fixes weighted bond contractions whose products span the sector algebra.

No product of fixed contractions is assumed to be fixed.  The fixed
contractions first give a positive-definite fixed family.  Wolf's
density-block description then bounds the dimension of the products of fixed
points, which forces every sector matrix to be fixed.

Source application: arXiv:1606.00608, Appendix C.4, lines 1980--1995. -/
theorem eq_id_of_weightedVerticalBondContractions_fixed_of_traceAdjointSchwarz
    {g D L : ℕ} {dim : Fin g → ℕ}
    (m : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (F : VerticalSectorAlgebra dim →ₗ[ℂ] VerticalSectorAlgebra dim)
    (hL : 0 < L)
    (hF : Matrix.IsPositiveDirectSumMap F)
    (hTP : Matrix.IsTracePreservingDirectSumMap F)
    (hSchwarz : Matrix.IsSchwarzDirectSumMap
      (Matrix.directSumTraceAdjointMap F))
    (hSpan : WeightedVerticalBondContractionProductSpanTop m A L)
    (hFixed : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      F (weightedVerticalBondContraction m A X) =
        weightedVerticalBondContraction m A X) :
    F = LinearMap.id := by
  have hOne :=
    one_mem_product_span_of_weightedVerticalBondContractions m A hSpan
  obtain ⟨ρ, hρ, hρFixed⟩ :=
    hF.exists_posDef_fixedFamily_of_fixed_product_span
      hTP (weightedVerticalBondContraction m A) L hL hFixed hOne
  apply eq_id_of_weightedVerticalBondContractions_fixed_of_productSpan_finrank_le
    m A F hSpan hFixed
  exact fixedPointProductSpan_finrank_le_of_densityBlocks
    hF hTP hSchwarz hρ hρFixed L hL

end MPOTensor
end

end

section

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
  have hTbarpos (X : VerticalSectorAlgebra h.dim₁)
      (hX : IsVerticalSectorPosSemidef X) :
      IsVerticalSectorPosSemidef (h.Tbar X) := by
    exact transportedVerticalSectorT_posSemidef
      h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.hMult₁ h.hWeight₁ h.U₁ h.U₂ h.T h.hTCPTP X hX
  have hSbarpos (X : VerticalSectorAlgebra h.dim₂)
      (hX : IsVerticalSectorPosSemidef X) :
      IsVerticalSectorPosSemidef (h.Sbar X) := by
    exact transportedVerticalSectorS_posSemidef
      h.dim₁ h.mult₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₂ h.hWeight₂ h.U₁ h.U₂ h.S h.hSCPTP X hX
  have hF₁pos : Matrix.IsPositiveDirectSumMap h.SbarTbar := by
    intro X hX
    exact hSbarpos (h.Tbar X) (hTbarpos X hX)
  have hF₂pos : Matrix.IsPositiveDirectSumMap h.TbarSbar := by
    intro X hX
    exact hTbarpos (h.Sbar X) (hSbarpos X hX)
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
end

end

section

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor

/-- The two transported vertical-sector algebras have matched simple summands,
and their mutually inverse maps act by conjugation with the same unitaries.

Source: CPSV16, arXiv:1606.00608, Appendix C.4, line 1997. The multiplicity
and coefficient comparison at lines 2001--2008 is not asserted here. -/
theorem transportedVerticalSector_exists_unitaryBlockEquiv
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :
    ∃ sigma : Fin g₁ ≃ Fin g₂, ∃ hDim : ∀ i, h.dim₁ i = h.dim₂ (sigma i),
      ∃ V : ∀ i, Matrix.unitaryGroup (Fin (h.dim₂ (sigma i))) ℂ,
        (∀ (i : Fin g₁) (X : Matrix (Fin (h.dim₁ i)) (Fin (h.dim₁ i)) ℂ),
            h.Tbar (Pi.single i X) = Pi.single (sigma i)
              ((V i : Matrix (Fin (h.dim₂ (sigma i))) (Fin (h.dim₂ (sigma i))) ℂ) *
                Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) X *
                  (V i : Matrix (Fin (h.dim₂ (sigma i))) (Fin (h.dim₂ (sigma i))) ℂ)ᴴ)) ∧
          ∀ (i : Fin g₁) (Y : Matrix (Fin (h.dim₂ (sigma i))) (Fin (h.dim₂ (sigma i))) ℂ),
            h.Sbar (Pi.single (sigma i) Y) = Pi.single i
              ((Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i))).symm
                ((V i : Matrix (Fin (h.dim₂ (sigma i))) (Fin (h.dim₂ (sigma i))) ℂ)ᴴ * Y *
                  (V i : Matrix (Fin (h.dim₂ (sigma i))) (Fin (h.dim₂ (sigma i))) ℂ))) := by
  classical
  let : ∀ i, NeZero (h.dim₁ i) := fun i ↦ ⟨(h.hBNT₁.blocks_dim_pos i).ne'⟩
  let : ∀ j, NeZero (h.dim₂ j) := fun j ↦ ⟨(h.hBNT₂.blocks_dim_pos j).ne'⟩
  have hTbar : Matrix.IsKrausDirectSumMap h.Tbar := by
    exact transportedVerticalSectorT_isKrausDirectSumMap
      h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.hMult₁ h.hWeight₁
      h.U₁ h.U₂ h.T h.hTCPTP.isKrausCP
  have hSbar : Matrix.IsKrausDirectSumMap h.Sbar := by
    exact transportedVerticalSectorS_isKrausDirectSumMap
      h.dim₁ h.mult₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₂ h.hWeight₂
      h.U₁ h.U₂ h.S h.hSCPTP.isKrausCP
  obtain ⟨_, _, hTbarTP, hSbarTP⟩ :=
    transportedVerticalSector_composites_tracePreserving h
  obtain ⟨hST, hTS⟩ := transportedVerticalSector_composites_eq_id h
  obtain ⟨sigma, hDim, V, hVT, hVS⟩ :=
    Matrix.exists_blockEquiv_dim_eq_unitary_forward_of_mutual_inverse_kraus_direct_sum_maps
      h.Tbar h.Sbar hTbar hSbar hTbarTP hSbarTP hST hTS
  exact ⟨sigma, hDim, V, hVT, hVS⟩

end MPOTensor
end

end
