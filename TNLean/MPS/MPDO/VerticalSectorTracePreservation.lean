/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.TraceNonincreasingDirectSum
import TNLean.MPS.MPDO.VerticalSectorFixedGenerators
import TNLean.MPS.MPDO.VerticalSectorGeneration
import TNLean.MPS.MPDO.VerticalSectorTraceLoss

/-!
# Trace preservation of the transported vertical-sector maps

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

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Appendix C.4,
  lines 1974--1980 and 1980--1995.
* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Propositions 6.3
  and 6.9.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor

namespace VerticalSectorHypotheses

/-- The transported vertical-sector refinement map preserves positivity under
the strong Appendix C.4 hypotheses.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4,
lines 1972--1979. -/
theorem Tbar_posSemidef
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D))
    (X : VerticalSectorAlgebra h.dim₁)
    (hX : IsVerticalSectorPosSemidef X) :
    IsVerticalSectorPosSemidef (h.Tbar X) := by
  exact transportedVerticalSectorT_posSemidef
    h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.hMult₁ h.hWeight₁
    h.U₁ h.U₂ h.T h.hTCPTP X hX

/-- The transported vertical-sector coarse-graining map preserves positivity
under the strong Appendix C.4 hypotheses.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4,
lines 1972--1979. -/
theorem Sbar_posSemidef
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D))
    (X : VerticalSectorAlgebra h.dim₂)
    (hX : IsVerticalSectorPosSemidef X) :
    IsVerticalSectorPosSemidef (h.Sbar X) := by
  exact transportedVerticalSectorS_posSemidef
    h.dim₁ h.mult₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₂ h.hWeight₂
    h.U₁ h.U₂ h.S h.hSCPTP X hX

/-- The coarse-graining--refinement square composite preserves positivity on
the first vertical-sector algebra.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1980. -/
theorem SbarTbar_isPositiveDirectSumMap
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :
    Matrix.IsPositiveDirectSumMap h.SbarTbar := by
  intro X hX
  exact h.Sbar_posSemidef (h.Tbar X) (h.Tbar_posSemidef X hX)

/-- The refinement--coarse-graining square composite preserves positivity on
the second vertical-sector algebra.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1980. -/
theorem TbarSbar_isPositiveDirectSumMap
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :
    Matrix.IsPositiveDirectSumMap h.TbarSbar := by
  intro X hX
  exact h.Tbar_posSemidef (h.Sbar X) (h.Sbar_posSemidef X hX)

end VerticalSectorHypotheses

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
  have hTbarpos := h.Tbar_posSemidef
  have hSbarpos := h.Sbar_posSemidef
  have hF₁pos := h.SbarTbar_isPositiveDirectSumMap
  have hF₂pos := h.TbarSbar_isPositiveDirectSumMap
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
