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

/-- The BNT product-span formulation agrees with the pointwise product family
used by the direct-sum trace criterion. -/
private theorem one_mem_product_span_of_weightedVerticalBondContractions
    {g D L : ℕ} {dim : Fin g → ℕ}
    (m : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (hSpan : WeightedVerticalBondContractionProductSpanTop m A L) :
    (1 : VerticalSectorAlgebra dim) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → Matrix (Fin D) (Fin D) ℂ ↦
        (List.ofFn fun t ↦ weightedVerticalBondContraction m A (x t)).prod) := by
  have hOneRaw : (1 : VerticalSectorAlgebra dim) ∈
      Submodule.span ℂ (Set.range
        (weightedVerticalBondContractionProduct (L := L) m A)) := by
    rw [hSpan]
    exact Submodule.mem_top
  have hRange : Set.range (weightedVerticalBondContractionProduct
      (L := L) m A) =
      Set.range (fun x : Fin L → Matrix (Fin D) (Fin D) ℂ ↦
        (List.ofFn fun t ↦ weightedVerticalBondContraction m A (x t)).prod) := by
    ext Y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      funext α
      change ((List.ofFn fun t ↦
          weightedVerticalBondContraction m A (x t)).prod) α =
        (List.ofFn fun t ↦ weightedVerticalBondContraction m A (x t) α).prod
      rw [Pi.list_prod_apply, List.map_ofFn]
      rfl
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      funext α
      change (List.ofFn fun t ↦
          weightedVerticalBondContraction m A (x t) α).prod =
        ((List.ofFn fun t ↦ weightedVerticalBondContraction m A (x t)).prod) α
      rw [Pi.list_prod_apply, List.map_ofFn]
      rfl
  rw [← hRange]
  exact hOneRaw

/-- The transported coarse-graining and refinement maps, as well as their two
square composites, preserve the appropriate total sector traces.

The proof uses the source hypotheses from arXiv:1606.00608, Appendix C.4.
Lines 1974--1980 supply the fixed vertical contractions; lines 1980--1995
supply the BNT spanning context.  The product span is used only to force full
support of a positive mean-ergodic fixed point; it is not used to claim that
products of fixed points are fixed. -/
theorem transportedVerticalSector_composites_tracePreserving
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (hBNT₁ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
      (fun α ↦ ⟨dim₁ α, A₁ α⟩))
    (hBNT₂ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor (blockTwo M))
      (fun β ↦ ⟨dim₂ β, A₂ β⟩))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hTCPTP : IsKrausCPTP T)
    (hSCPTP : IsKrausCPTP S)
    (hForward₁ : ∀ ab, U₁ * verticalTensor M ab * U₁ᴴ =
      verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hForward₂ : ∀ ab, U₂ * verticalTensor (blockTwo M) ab * U₂ᴴ =
      verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (hTphys : ∀ X, T (physClose1 M X) = physClose2 M X)
    (hSphys : ∀ X, S (physClose2 M X) = physClose1 M X) :
    Matrix.IsTracePreservingDirectSumMap
        ((transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S).comp
          (transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T)) ∧
      Matrix.IsTracePreservingDirectSumMap
        ((transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T).comp
          (transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S)) ∧
      Matrix.IsTracePreservingBetweenDirectSums
        (transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T) ∧
      Matrix.IsTracePreservingBetweenDirectSums
        (transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S) := by
  classical
  let Tbar := transportedVerticalSectorT
    dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T
  let Sbar := transportedVerticalSectorS
    dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S
  let F₁ := Sbar.comp Tbar
  let F₂ := Tbar.comp Sbar
  have hTbarpos (X : VerticalSectorAlgebra dim₁)
      (hX : IsVerticalSectorPosSemidef X) :
      IsVerticalSectorPosSemidef (Tbar X) := by
    exact transportedVerticalSectorT_posSemidef
      dim₁ mult₁ weight₁ dim₂ mult₂ hMult₁ hWeight₁ U₁ U₂ T hTCPTP X hX
  have hSbarpos (X : VerticalSectorAlgebra dim₂)
      (hX : IsVerticalSectorPosSemidef X) :
      IsVerticalSectorPosSemidef (Sbar X) := by
    exact transportedVerticalSectorS_posSemidef
      dim₁ mult₁ dim₂ mult₂ weight₂ hMult₂ hWeight₂ U₁ U₂ S hSCPTP X hX
  have hF₁pos : Matrix.IsPositiveDirectSumMap F₁ := by
    intro X hX
    exact hSbarpos (Tbar X) (hTbarpos X hX)
  have hF₂pos : Matrix.IsPositiveDirectSumMap F₂ := by
    intro X hX
    exact hTbarpos (Sbar X) (hSbarpos X hX)
  have hTbarle (X : VerticalSectorAlgebra dim₁)
      (hX : IsVerticalSectorPosSemidef X) :
      verticalSectorTrace (Tbar X) ≤ verticalSectorTrace X :=
    transportedVerticalSectorT_trace_le
      dim₁ mult₁ weight₁ dim₂ mult₂ hMult₁ hWeight₁
      U₁ hU₁ U₂ hU₂ T hTCPTP X hX
  have hSbarle (X : VerticalSectorAlgebra dim₂)
      (hX : IsVerticalSectorPosSemidef X) :
      verticalSectorTrace (Sbar X) ≤ verticalSectorTrace X :=
    transportedVerticalSectorS_trace_le
      dim₁ mult₁ dim₂ mult₂ weight₂ hMult₂ hWeight₂
      U₁ hU₁ U₂ hU₂ S hSCPTP X hX
  have hTbarTNI : Matrix.IsDirectSumTraceNonincreasing Tbar := by
    intro X hX
    exact hTbarle X hX
  have hSbarTNI : Matrix.IsDirectSumTraceNonincreasing Sbar := by
    intro X hX
    exact hSbarle X hX
  have hF₁TNI : Matrix.IsDirectSumTraceNonincreasing F₁ := by
    intro X hX
    exact (hSbarle (Tbar X) (hTbarpos X hX)).trans (hTbarle X hX)
  have hF₂TNI : Matrix.IsDirectSumTraceNonincreasing F₂ := by
    intro X hX
    exact (hTbarle (Sbar X) (hSbarpos X hX)).trans (hSbarle X hX)
  obtain ⟨L₁, hL₁, hSpan₁⟩ :=
    exists_positive_verticalMultiplicityTraceBondContractionProductSpanTop_of_bnt
      hBNT₁ weight₁ hMult₁ hWeight₁
  obtain ⟨L₂, hL₂, hSpan₂⟩ :=
    exists_positive_verticalMultiplicityTraceBondContractionProductSpanTop_of_bnt
      hBNT₂ weight₂ hMult₂ hWeight₂
  let V₁ := weightedVerticalBondContraction
    (verticalMultiplicityTrace weight₁) A₁
  let V₂ := weightedVerticalBondContraction
    (verticalMultiplicityTrace weight₂) A₂
  have hV₁fixed (X : Matrix (Fin D) (Fin D) ℂ) : F₁ (V₁ X) = V₁ X := by
    change F₁ (fun α ↦ verticalMultiplicityTrace weight₁ α •
      MPSTensor.contractBondMatrix (A₁ α) X) =
        fun α ↦ verticalMultiplicityTrace weight₁ α •
          MPSTensor.contractBondMatrix (A₁ α) X
    simpa only [F₁, Tbar, Sbar] using
      transportedVerticalSectorS_comp_T_fixed_contractBondMatrix_trace_smul
        dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₁ hWeight₁ hMult₂ hWeight₂
        M A₁ A₂ U₁ U₂ T S hForward₁ hReconstruct₁ hForward₂ hReconstruct₂ X
        (hTphys X) (hSphys X)
  have hV₂fixed (X : Matrix (Fin D) (Fin D) ℂ) : F₂ (V₂ X) = V₂ X := by
    change F₂ (fun β ↦ verticalMultiplicityTrace weight₂ β •
      MPSTensor.contractBondMatrix (A₂ β) X) =
        fun β ↦ verticalMultiplicityTrace weight₂ β •
          MPSTensor.contractBondMatrix (A₂ β) X
    simpa only [F₂, Tbar, Sbar] using
      transportedVerticalSectorT_comp_S_fixed_contractBondMatrix_trace_smul
        dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₁ hWeight₁ hMult₂ hWeight₂
        M A₁ A₂ U₁ U₂ T S hForward₁ hReconstruct₁ hForward₂ hReconstruct₂ X
        (hTphys X) (hSphys X)
  have hOne₁ : (1 : VerticalSectorAlgebra dim₁) ∈
      Submodule.span ℂ (Set.range fun x : Fin L₁ → Matrix (Fin D) (Fin D) ℂ ↦
        (List.ofFn fun t ↦ V₁ (x t)).prod) := by
    simpa only [V₁] using
      one_mem_product_span_of_weightedVerticalBondContractions
        (verticalMultiplicityTrace weight₁) A₁ hSpan₁
  have hOne₂ : (1 : VerticalSectorAlgebra dim₂) ∈
      Submodule.span ℂ (Set.range fun x : Fin L₂ → Matrix (Fin D) (Fin D) ℂ ↦
        (List.ofFn fun t ↦ V₂ (x t)).prod) := by
    simpa only [V₂] using
      one_mem_product_span_of_weightedVerticalBondContractions
        (verticalMultiplicityTrace weight₂) A₂ hSpan₂
  have hF₁trace :=
    hF₁pos.tracePreserving_of_traceNonincreasing_of_fixed_product_span
      hF₁TNI V₁ L₁ hL₁ hV₁fixed hOne₁
  have hF₂trace :=
    hF₂pos.tracePreserving_of_traceNonincreasing_of_fixed_product_span
      hF₂TNI V₂ L₂ hL₂ hV₂fixed hOne₂
  have hTbarTrace : Matrix.IsTracePreservingBetweenDirectSums Tbar :=
    Matrix.isTracePreservingBetweenDirectSums_of_comp_of_traceNonincreasing
      hTbarpos hTbarTNI hSbarTNI hF₁trace
  have hSbarTrace : Matrix.IsTracePreservingBetweenDirectSums Sbar :=
    Matrix.isTracePreservingBetweenDirectSums_of_comp_of_traceNonincreasing
      hSbarpos hSbarTNI hTbarTNI hF₂trace
  exact ⟨hF₁trace, hF₂trace, hTbarTrace, hSbarTrace⟩

end MPOTensor
