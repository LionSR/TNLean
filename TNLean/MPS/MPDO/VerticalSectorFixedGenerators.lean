/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalSectorCoordinates

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
-/

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
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hForward₁ : ∀ ab, U₁ * verticalTensor M ab * U₁ᴴ =
      verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hForward₂ : ∀ ab, U₂ * verticalTensor (blockTwo M) ab * U₂ᴴ =
      verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hT : T (physClose1 M X) = physClose2 M X)
    (hS : S (physClose2 M X) = physClose1 M X) :
    ((transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S).comp
      (transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T))
        (fun α => verticalMultiplicityTrace weight₁ α •
          MPSTensor.contractBondMatrix (A₁ α) X) =
      fun α => verticalMultiplicityTrace weight₁ α •
        MPSTensor.contractBondMatrix (A₁ α) X := by
  simp only [LinearMap.comp_apply]
  rw [transportedVerticalSectorT_contractBondMatrix_trace_smul
    dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₁ hWeight₁ M A₁ A₂ U₁ U₂ T
    hReconstruct₁ hForward₂ X hT]
  exact transportedVerticalSectorS_contractBondMatrix_trace_smul
    dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₂ hWeight₂ M A₁ A₂ U₁ U₂ S
    hForward₁ hReconstruct₂ X hS

/-- Every multiplicity-trace-scaled two-site vertical BNT bond contraction is
fixed by the transported refinement--coarse-graining composite.

This proves only the inclusion of the two-site contraction family in the
fixed-point space.  The conclusion that the composite is the identity uses
the later fixed-point structure argument of Appendix C.4, lines 1980--1993.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1980. -/
theorem transportedVerticalSectorT_comp_S_fixed_contractBondMatrix_trace_smul
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
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hForward₁ : ∀ ab, U₁ * verticalTensor M ab * U₁ᴴ =
      verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hForward₂ : ∀ ab, U₂ * verticalTensor (blockTwo M) ab * U₂ᴴ =
      verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hT : T (physClose1 M X) = physClose2 M X)
    (hS : S (physClose2 M X) = physClose1 M X) :
    ((transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T).comp
      (transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S))
        (fun β => verticalMultiplicityTrace weight₂ β •
          MPSTensor.contractBondMatrix (A₂ β) X) =
      fun β => verticalMultiplicityTrace weight₂ β •
        MPSTensor.contractBondMatrix (A₂ β) X := by
  simp only [LinearMap.comp_apply]
  rw [transportedVerticalSectorS_contractBondMatrix_trace_smul
    dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₂ hWeight₂ M A₁ A₂ U₁ U₂ S
    hForward₁ hReconstruct₂ X hS]
  exact transportedVerticalSectorT_contractBondMatrix_trace_smul
    dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₁ hWeight₁ M A₁ A₂ U₁ U₂ T
    hReconstruct₁ hForward₂ X hT

end MPOTensor
