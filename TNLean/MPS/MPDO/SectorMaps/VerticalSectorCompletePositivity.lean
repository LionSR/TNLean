/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SectorMaps.VerticalSectorCoordinates
import QICLean.Channel.FixedPoint.TraceNonincreasingDirectSum
import TNLean.MPS.MPDO.SectorMaps.VerticalSectorGeneration
import TNLean.MPS.MPDO.SectorMaps.VerticalSectorTraceLoss

/-!
# Fixed generators of the transported vertical-sector composites

The transported refinement map sends each multiplicity-trace-scaled
one-site vertical BNT bond contraction to its two-site counterpart, and the
transported coarse-graining map sends it back.  Thus these contractions are
fixed by the coarse-graining--refinement composite.  The reverse composite
fixes the two-site contractions in the same way.

These conclusions concern only the two contraction families.  They do not
assert that either composite is the identity on the full sector algebra.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1974--1980.

## Trace preservation of the transported vertical-sector maps

The two square composites of the transported vertical-sector maps preserve
the total sector trace.  Consequently, the trace-nonincreasing inequalities
for the two individual maps become equalities.  Positivity and trace
nonincrease give bounded
orbits.  The mean-ergodic image of the identity has maximal support among
fixed points, while the fixed vertical bond contractions have
positive-length products spanning the sector algebra.  Their common support
must therefore be the identity, and the trace-loss functional vanishes.

No product of fixed contractions is assumed to be fixed, and neither
multiplicativity nor invertibility enters the argument.

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Appendix C.4,
  lines 1974--1980 and 1980--1995.
* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Propositions 6.3
  and 6.9.

## Complete positivity of the transported vertical-sector maps

The normalized vertical-sector embedding is a controlled state preparation,
and the vertical-sector retraction is a controlled partial trace.  After
identifying the retained physical coordinates with the corresponding direct
sums, these maps can be composed with the completely positive physical
refinement and coarse-graining maps.  Thus both transported vertical-sector
maps are completely positive between finite sums of matrix algebras.

The two square composites are trace preserving by the independent
maximal-support argument established earlier.  Complete positivity therefore
gives the Schwarz inequalities for their trace adjoints.

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Definition 4.1 and Appendix C.4, lines 1955--1995.
-/

section

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor

/-- Every multiplicity-trace-scaled one-site vertical BNT bond contraction is
fixed by the transported coarse-graining--refinement composite.

This proves only the inclusion of the one-site contraction family in the
fixed-point space.  The conclusion that the composite is the identity uses
the later fixed-point structure argument of Appendix C.4, lines 1980--1993.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1980. -/
theorem transportedVerticalSectorS_comp_T_fixed_contractBondMatrix_trace_smul
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorFixedGeneratorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    h.SbarTbar (fun α => verticalMultiplicityTrace h.weight₁ α •
      MPSTensor.contractBondMatrix (h.A₁ α) X) =
      fun α => verticalMultiplicityTrace h.weight₁ α •
        MPSTensor.contractBondMatrix (h.A₁ α) X := by
  simp only [VerticalSectorFixedGeneratorHypotheses.SbarTbar,
    VerticalSectorFixedGeneratorHypotheses.Sbar,
    VerticalSectorFixedGeneratorHypotheses.Tbar, LinearMap.comp_apply]
  rw [transportedVerticalSectorT_contractBondMatrix_trace_smul
    h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₁ h.hWeight₁
    h.M h.A₁ h.A₂ h.U₁ h.U₂ h.T h.hReconstruct₁ h.hForward₂ X (h.hTphys X)]
  exact transportedVerticalSectorS_contractBondMatrix_trace_smul
    h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₂ h.hWeight₂
    h.M h.A₁ h.A₂ h.U₁ h.U₂ h.S h.hForward₁ h.hReconstruct₂ X (h.hSphys X)

/-- Every multiplicity-trace-scaled two-site vertical BNT bond contraction is
fixed by the transported refinement--coarse-graining composite.

This proves only the inclusion of the two-site contraction family in the
fixed-point space.  The conclusion that the composite is the identity uses
the later fixed-point structure argument of Appendix C.4, lines 1980--1993.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1980. -/
theorem transportedVerticalSectorT_comp_S_fixed_contractBondMatrix_trace_smul
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorFixedGeneratorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    h.TbarSbar (fun β => verticalMultiplicityTrace h.weight₂ β •
      MPSTensor.contractBondMatrix (h.A₂ β) X) =
      fun β => verticalMultiplicityTrace h.weight₂ β •
        MPSTensor.contractBondMatrix (h.A₂ β) X := by
  simp only [VerticalSectorFixedGeneratorHypotheses.TbarSbar,
    VerticalSectorFixedGeneratorHypotheses.Tbar,
    VerticalSectorFixedGeneratorHypotheses.Sbar, LinearMap.comp_apply]
  rw [transportedVerticalSectorS_contractBondMatrix_trace_smul
    h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₂ h.hWeight₂
    h.M h.A₁ h.A₂ h.U₁ h.U₂ h.S h.hForward₁ h.hReconstruct₂ X (h.hSphys X)]
  exact transportedVerticalSectorT_contractBondMatrix_trace_smul
    h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₁ h.hWeight₁
    h.M h.A₁ h.A₂ h.U₁ h.U₂ h.T h.hReconstruct₁ h.hForward₂ X (h.hTphys X)

end MPOTensor
end

end

section

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor

/-- The transported coarse-graining and refinement maps, as well as their two
square composites, preserve the appropriate total sector traces.

The proof uses the source hypotheses from arXiv:1606.00608, Appendix C.4.
Lines 1974--1980 supply the fixed vertical contractions; lines 1980--1995
supply the BNT spanning context.  The product span is used only to force full
support of a positive mean-ergodic fixed point; it is not used to claim that
products of fixed points are fixed. -/
theorem transportedVerticalSector_composites_tracePreserving
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :
    Matrix.IsTracePreservingDirectSumMap h.SbarTbar ∧
      Matrix.IsTracePreservingDirectSumMap h.TbarSbar ∧
      Matrix.IsTracePreservingBetweenDirectSums h.Tbar ∧
      Matrix.IsTracePreservingBetweenDirectSums h.Sbar := by
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
  have hTbarle (X : VerticalSectorAlgebra h.dim₁)
      (hX : IsVerticalSectorPosSemidef X) :
      verticalSectorTrace (h.Tbar X) ≤ verticalSectorTrace X :=
    transportedVerticalSectorT_trace_le
      h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.hMult₁ h.hWeight₁
      h.U₁ h.hU₁ h.U₂ h.hU₂ h.T h.hTCPTP X hX
  have hSbarle (X : VerticalSectorAlgebra h.dim₂)
      (hX : IsVerticalSectorPosSemidef X) :
      verticalSectorTrace (h.Sbar X) ≤ verticalSectorTrace X :=
    transportedVerticalSectorS_trace_le
      h.dim₁ h.mult₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₂ h.hWeight₂
      h.U₁ h.hU₁ h.U₂ h.hU₂ h.S h.hSCPTP X hX
  have hTbarTNI : Matrix.IsTraceNonincreasingBetweenDirectSums h.Tbar := by
    intro X hX
    exact hTbarle X hX
  have hSbarTNI : Matrix.IsTraceNonincreasingBetweenDirectSums h.Sbar := by
    intro X hX
    exact hSbarle X hX
  have hF₁TNI : Matrix.IsTraceNonincreasingBetweenDirectSums h.SbarTbar := by
    intro X hX
    exact (hSbarle (h.Tbar X) (hTbarpos X hX)).trans (hTbarle X hX)
  have hF₂TNI : Matrix.IsTraceNonincreasingBetweenDirectSums h.TbarSbar := by
    intro X hX
    exact (hTbarle (h.Sbar X) (hSbarpos X hX)).trans (hSbarle X hX)
  obtain ⟨L₁, hL₁, hSpan₁⟩ :=
    exists_positive_verticalMultiplicityTraceBondContractionProductSpanTop_of_bnt
      h.hBNT₁ h.weight₁ h.hMult₁ h.hWeight₁
  obtain ⟨L₂, hL₂, hSpan₂⟩ :=
    exists_positive_verticalMultiplicityTraceBondContractionProductSpanTop_of_bnt
      h.hBNT₂ h.weight₂ h.hMult₂ h.hWeight₂
  let V₁ := weightedVerticalBondContraction
    (verticalMultiplicityTrace h.weight₁) h.A₁
  let V₂ := weightedVerticalBondContraction
    (verticalMultiplicityTrace h.weight₂) h.A₂
  have hV₁fixed (X : Matrix (Fin D) (Fin D) ℂ) : h.SbarTbar (V₁ X) = V₁ X := by
    change h.SbarTbar (fun α ↦ verticalMultiplicityTrace h.weight₁ α •
      MPSTensor.contractBondMatrix (h.A₁ α) X) =
        fun α ↦ verticalMultiplicityTrace h.weight₁ α •
          MPSTensor.contractBondMatrix (h.A₁ α) X
    exact transportedVerticalSectorS_comp_T_fixed_contractBondMatrix_trace_smul
      h.toVerticalSectorFixedGeneratorHypotheses X
  have hV₂fixed (X : Matrix (Fin D) (Fin D) ℂ) : h.TbarSbar (V₂ X) = V₂ X := by
    change h.TbarSbar (fun β ↦ verticalMultiplicityTrace h.weight₂ β •
      MPSTensor.contractBondMatrix (h.A₂ β) X) =
        fun β ↦ verticalMultiplicityTrace h.weight₂ β •
          MPSTensor.contractBondMatrix (h.A₂ β) X
    exact transportedVerticalSectorT_comp_S_fixed_contractBondMatrix_trace_smul
      h.toVerticalSectorFixedGeneratorHypotheses X
  have hOne₁ : (1 : VerticalSectorAlgebra h.dim₁) ∈
      Submodule.span ℂ (Set.range fun x : Fin L₁ → Matrix (Fin D) (Fin D) ℂ ↦
        (List.ofFn fun t ↦ V₁ (x t)).prod) := by
    simpa only [V₁] using
      one_mem_product_span_of_weightedVerticalBondContractions
        (verticalMultiplicityTrace h.weight₁) h.A₁ hSpan₁
  have hOne₂ : (1 : VerticalSectorAlgebra h.dim₂) ∈
      Submodule.span ℂ (Set.range fun x : Fin L₂ → Matrix (Fin D) (Fin D) ℂ ↦
        (List.ofFn fun t ↦ V₂ (x t)).prod) := by
    simpa only [V₂] using
      one_mem_product_span_of_weightedVerticalBondContractions
        (verticalMultiplicityTrace h.weight₂) h.A₂ hSpan₂
  have hF₁trace :=
    hF₁pos.tracePreserving_of_traceNonincreasing_of_fixed_product_span
      hF₁TNI V₁ L₁ hL₁ hV₁fixed hOne₁
  have hF₂trace :=
    hF₂pos.tracePreserving_of_traceNonincreasing_of_fixed_product_span
      hF₂TNI V₂ L₂ hL₂ hV₂fixed hOne₂
  have hTbarTrace : Matrix.IsTracePreservingBetweenDirectSums h.Tbar :=
    Matrix.isTracePreservingBetweenDirectSums_of_comp_of_traceNonincreasing
      hTbarpos hTbarTNI hSbarTNI
        (Matrix.isTracePreservingBetweenDirectSums_iff_isTracePreservingDirectSumMap.mpr
          hF₁trace)
  have hSbarTrace : Matrix.IsTracePreservingBetweenDirectSums h.Sbar :=
    Matrix.isTracePreservingBetweenDirectSums_of_comp_of_traceNonincreasing
      hSbarpos hSbarTNI hTbarTNI
        (Matrix.isTracePreservingBetweenDirectSums_iff_isTracePreservingDirectSumMap.mpr
          hF₂trace)
  exact ⟨hF₁trace, hF₂trace, hTbarTrace, hSbarTrace⟩

end MPOTensor
end

end

section

open scoped Matrix MatrixOrder ComplexOrder

noncomputable section

namespace MPOTensor

/-- Transporting a completely positive refinement map through the retained
vertical coordinates preserves complete positivity.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem transportTToVerticalCoordinates_isKrausCP
    {d R₁ R₂ : ℕ}
    (U₁ : Matrix (Fin R₁) (Fin d) ℂ)
    (U₂ : Matrix (Fin R₂) (Fin (d * d)) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hT : IsKrausCP T) :
    IsKrausCP (transportTToVerticalCoordinates U₁ U₂ T) := by
  unfold transportTToVerticalCoordinates
  apply isKrausCP_comp
  · apply isKrausCP_comp
    · apply isKrausCP_comp
      · exact singleKrausMap_isKrausCP U₁ᴴ
      · exact hT
    · exact (Matrix.equivReindexMap_isKrausCPTP
        (blockedIndexEquiv d).symm).isKrausCP
  · exact singleKrausMap_isKrausCP U₂

/-- Transporting a completely positive coarse-graining map through the
retained vertical coordinates preserves complete positivity.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem transportSToVerticalCoordinates_isKrausCP
    {d R₁ R₂ : ℕ}
    (U₁ : Matrix (Fin R₁) (Fin d) ℂ)
    (U₂ : Matrix (Fin R₂) (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hS : IsKrausCP S) :
    IsKrausCP (transportSToVerticalCoordinates U₁ U₂ S) := by
  unfold transportSToVerticalCoordinates
  apply isKrausCP_comp
  · apply isKrausCP_comp
    · exact isKrausCP_comp (singleKrausMap_isKrausCP U₂ᴴ)
        (Matrix.equivReindexMap_isKrausCPTP
          (blockedIndexEquiv d)).isKrausCP
    · exact hS
  · exact singleKrausMap_isKrausCP U₁

/-- In retained coordinates, putting a vertical-sector family on the block
diagonal is block-diagonal embedding followed by the canonical reindexing.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
theorem verticalSectorBlockDiagonal_eq_equivReindexMap_comp_embedding
    {g : ℕ} (dim mult : Fin g → ℕ) :
    verticalSectorBlockDiagonal dim mult =
      (Matrix.equivReindexMap (verticalSectorFinEquiv dim mult)).comp
        Matrix.directSumDiagonalEmbedding :=
  rfl

/-- In retained coordinates, extracting the vertical-sector blocks is the
canonical inverse reindexing followed by diagonal-block compression.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
theorem verticalSectorBlocks_eq_compression_comp_equivReindexMap
    {g : ℕ} (dim mult : Fin g → ℕ) :
    verticalSectorBlocks dim mult =
      Matrix.directSumDiagonalCompression.comp
        (Matrix.equivReindexMap (verticalSectorFinEquiv dim mult).symm) :=
  rfl

/-- The canonical full-matrix extension of the transported refinement map is
the composition of the normalized preparation, retained-coordinate changes,
physical refinement map, and partial trace.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem directSumMapExtension_transportedVerticalSectorT
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.directSumMapExtension
        (transportedVerticalSectorT
          dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T) =
      (Matrix.directSumMapExtension
        (verticalSectorPartialTrace dim₂ mult₂)).comp
        ((Matrix.equivReindexMap
          (verticalSectorFinEquiv dim₂ mult₂).symm).comp
          ((transportTToVerticalCoordinates U₁ U₂ T).comp
            ((Matrix.equivReindexMap
              (verticalSectorFinEquiv dim₁ mult₁)).comp
              (Matrix.directSumMapExtension
                (normalizedVerticalSectorEmbedding
                  dim₁ mult₁ weight₁))))) := by
  apply LinearMap.ext
  intro X
  rfl

/-- The canonical full-matrix extension of the transported coarse-graining
map is the composition of the normalized preparation, retained-coordinate
changes, physical coarse-graining map, and partial trace.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem directSumMapExtension_transportedVerticalSectorS
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ) :
    Matrix.directSumMapExtension
        (transportedVerticalSectorS
          dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S) =
      (Matrix.directSumMapExtension
        (verticalSectorPartialTrace dim₁ mult₁)).comp
        ((Matrix.equivReindexMap
          (verticalSectorFinEquiv dim₁ mult₁).symm).comp
          ((transportSToVerticalCoordinates U₁ U₂ S).comp
            ((Matrix.equivReindexMap
              (verticalSectorFinEquiv dim₂ mult₂)).comp
              (Matrix.directSumMapExtension
                (normalizedVerticalSectorEmbedding
                  dim₂ mult₂ weight₂))))) := by
  apply LinearMap.ext
  intro X
  rfl

/-- The transported refinement map is completely positive between the finite
sums of vertical simple-sector matrix algebras.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem transportedVerticalSectorT_isKrausDirectSumMap
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hT : IsKrausCP T) :
    Matrix.IsKrausDirectSumMap
      (transportedVerticalSectorT
        dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T) := by
  rw [Matrix.IsKrausDirectSumMap,
    directSumMapExtension_transportedVerticalSectorT]
  have hPrep := normalizedVerticalSectorEmbedding_isKrausDirectSumMap
    dim₁ mult₁ weight₁ hMult₁ hWeight₁
  have hReindex₁ := (Matrix.equivReindexMap_isKrausCPTP
    (verticalSectorFinEquiv dim₁ mult₁)).isKrausCP
  have hTransport := transportTToVerticalCoordinates_isKrausCP U₁ U₂ T hT
  have hReindex₂ := (Matrix.equivReindexMap_isKrausCPTP
    (verticalSectorFinEquiv dim₂ mult₂).symm).isKrausCP
  have hTrace := verticalSectorPartialTrace_isKrausDirectSumMap dim₂ mult₂
  exact isKrausCP_comp
    (isKrausCP_comp
      (isKrausCP_comp (isKrausCP_comp hPrep hReindex₁) hTransport)
      hReindex₂)
    hTrace

/-- The transported coarse-graining map is completely positive between the
finite sums of vertical simple-sector matrix algebras.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem transportedVerticalSectorS_isKrausDirectSumMap
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hS : IsKrausCP S) :
    Matrix.IsKrausDirectSumMap
      (transportedVerticalSectorS
        dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S) := by
  rw [Matrix.IsKrausDirectSumMap,
    directSumMapExtension_transportedVerticalSectorS]
  have hPrep := normalizedVerticalSectorEmbedding_isKrausDirectSumMap
    dim₂ mult₂ weight₂ hMult₂ hWeight₂
  have hReindex₂ := (Matrix.equivReindexMap_isKrausCPTP
    (verticalSectorFinEquiv dim₂ mult₂)).isKrausCP
  have hTransport := transportSToVerticalCoordinates_isKrausCP U₁ U₂ S hS
  have hReindex₁ := (Matrix.equivReindexMap_isKrausCPTP
    (verticalSectorFinEquiv dim₁ mult₁).symm).isKrausCP
  have hTrace := verticalSectorPartialTrace_isKrausDirectSumMap dim₁ mult₁
  exact isKrausCP_comp
    (isKrausCP_comp
      (isKrausCP_comp (isKrausCP_comp hPrep hReindex₂) hTransport)
      hReindex₁)
    hTrace

/-- The trace adjoints of the two transported square composites satisfy the
Schwarz inequality under the tensor hypotheses of Appendix C.4.

Complete positivity follows from the Kraus forms of the normalized sector
preparations, physical maps, coordinate changes, and partial traces.  The
independent maximal-support argument gives trace preservation of the square
composites, so their trace adjoints are unital completely positive maps.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1995. -/
theorem transportedVerticalSector_composites_traceAdjointSchwarz
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :
    Matrix.IsSchwarzDirectSumMap
        (Matrix.directSumTraceAdjointMap h.SbarTbar) ∧
      Matrix.IsSchwarzDirectSumMap
        (Matrix.directSumTraceAdjointMap h.TbarSbar) := by
  obtain ⟨hSTTrace, hTSTrace, _, _⟩ :=
    transportedVerticalSector_composites_tracePreserving h
  have hT := transportedVerticalSectorT_isKrausDirectSumMap
    h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.hMult₁ h.hWeight₁
    h.U₁ h.U₂ h.T h.hTCPTP.isKrausCP
  have hS := transportedVerticalSectorS_isKrausDirectSumMap
    h.dim₁ h.mult₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₂ h.hWeight₂
    h.U₁ h.U₂ h.S h.hSCPTP.isKrausCP
  exact ⟨(hT.comp hS).directSumTraceAdjointMap_isSchwarz hSTTrace,
    (hS.comp hT).directSumTraceAdjointMap_isSchwarz hTSTrace⟩

end MPOTensor
end

end
