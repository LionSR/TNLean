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
    (transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S).comp
        (transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T) =
      LinearMap.id ∧
    (transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T).comp
        (transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S) =
      LinearMap.id := by
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
  obtain ⟨hF₁TP, hF₂TP, _, _⟩ :=
    transportedVerticalSector_composites_tracePreserving
      dim₁ mult₁ weight₁ dim₂ mult₂ weight₂
      hMult₁ hWeight₁ hMult₂ hWeight₂ M A₁ A₂ hBNT₁ hBNT₂
      U₁ U₂ hU₁ hU₂ T S hTCPTP hSCPTP
      hForward₁ hReconstruct₁ hForward₂ hReconstruct₂ hTphys hSphys
  obtain ⟨hF₁Schwarz, hF₂Schwarz⟩ :=
    transportedVerticalSector_composites_traceAdjointSchwarz
      dim₁ mult₁ weight₁ dim₂ mult₂ weight₂
      hMult₁ hWeight₁ hMult₂ hWeight₂ M A₁ A₂ hBNT₁ hBNT₂
      U₁ U₂ hU₁ hU₂ T S hTCPTP hSCPTP
      hForward₁ hReconstruct₁ hForward₂ hReconstruct₂ hTphys hSphys
  obtain ⟨L₁, hL₁, hSpan₁⟩ :=
    exists_positive_verticalMultiplicityTraceBondContractionProductSpanTop_of_bnt
      hBNT₁ weight₁ hMult₁ hWeight₁
  obtain ⟨L₂, hL₂, hSpan₂⟩ :=
    exists_positive_verticalMultiplicityTraceBondContractionProductSpanTop_of_bnt
      hBNT₂ weight₂ hMult₂ hWeight₂
  have hFixed₁ (X : Matrix (Fin D) (Fin D) ℂ) :
      F₁ (weightedVerticalBondContraction
        (verticalMultiplicityTrace weight₁) A₁ X) =
        weightedVerticalBondContraction
          (verticalMultiplicityTrace weight₁) A₁ X := by
    change F₁ (fun α ↦ verticalMultiplicityTrace weight₁ α •
      MPSTensor.contractBondMatrix (A₁ α) X) =
        fun α ↦ verticalMultiplicityTrace weight₁ α •
          MPSTensor.contractBondMatrix (A₁ α) X
    simpa only [F₁, Tbar, Sbar] using
      transportedVerticalSectorS_comp_T_fixed_contractBondMatrix_trace_smul
        dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₁ hWeight₁ hMult₂ hWeight₂
        M A₁ A₂ U₁ U₂ T S hForward₁ hReconstruct₁ hForward₂ hReconstruct₂ X
        (hTphys X) (hSphys X)
  have hFixed₂ (X : Matrix (Fin D) (Fin D) ℂ) :
      F₂ (weightedVerticalBondContraction
        (verticalMultiplicityTrace weight₂) A₂ X) =
        weightedVerticalBondContraction
          (verticalMultiplicityTrace weight₂) A₂ X := by
    change F₂ (fun β ↦ verticalMultiplicityTrace weight₂ β •
      MPSTensor.contractBondMatrix (A₂ β) X) =
        fun β ↦ verticalMultiplicityTrace weight₂ β •
          MPSTensor.contractBondMatrix (A₂ β) X
    simpa only [F₂, Tbar, Sbar] using
      transportedVerticalSectorT_comp_S_fixed_contractBondMatrix_trace_smul
        dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₁ hWeight₁ hMult₂ hWeight₂
        M A₁ A₂ U₁ U₂ T S hForward₁ hReconstruct₁ hForward₂ hReconstruct₂ X
        (hTphys X) (hSphys X)
  constructor
  · change F₁ = LinearMap.id
    exact eq_id_of_weightedVerticalBondContractions_fixed_of_traceAdjointSchwarz
      (verticalMultiplicityTrace weight₁) A₁ F₁ hL₁ hF₁pos hF₁TP hF₁Schwarz
      hSpan₁ hFixed₁
  · change F₂ = LinearMap.id
    exact eq_id_of_weightedVerticalBondContractions_fixed_of_traceAdjointSchwarz
      (verticalMultiplicityTrace weight₂) A₂ F₂ hL₂ hF₂pos hF₂TP hF₂Schwarz
      hSpan₂ hFixed₂

end MPOTensor
