/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalSectorTraceLoss

/-!
# Image preservation for transported vertical-sector maps

The matrices before the final compression of the transported refinement and
coarse-graining maps lie in the active vertical sectors on the bond
contractions of the corresponding vertical canonical forms.  Consequently,
the transported maps preserve total sector trace on these contraction
families.

The mathematical scope is documented in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

## Main results

* `precompressionVerticalSectorT_image_preservation`: the refinement
  precompression matrix of a one-site contraction lies in the active two-site
  sector.
* `precompressionVerticalSectorS_image_preservation`: the corresponding
  statement for coarse-graining.
* `transportedVerticalSectorT_trace_of_source_generated`: refinement preserves
  sector trace on the one-site contraction family.
* `transportedVerticalSectorS_trace_of_source_generated`: coarse-graining
  preserves sector trace on the two-site contraction family.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1955--1980.
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor

/-- The matrix before the final two-site compression lies in the active
two-site sector for every one-site BNT bond contraction.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1980. -/
theorem precompressionVerticalSectorT_image_preservation
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hT : T (physClose1 M X) = physClose2 M X) :
    U₂ᴴ * U₂ * precompressionVerticalSectorT dim₁ mult₁ weight₁ U₁ T
        (fun α => verticalMultiplicityTrace weight₁ α •
          MPSTensor.contractBondMatrix (A₁ α) X) =
      precompressionVerticalSectorT dim₁ mult₁ weight₁ U₁ T
        (fun α => verticalMultiplicityTrace weight₁ α •
          MPSTensor.contractBondMatrix (A₁ α) X) := by
  unfold precompressionVerticalSectorT
  rw [normalizedRetainedVerticalSectorEmbedding_trace_smul
    dim₁ mult₁ weight₁ hMult₁ hWeight₁]
  rw [← contractBondMatrix_verticalAssembledTensor_eq_sectorBlockDiagonal]
  rw [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose]
  rw [← physClose1_eq_of_vertical_reconstruction M
    (verticalAssembledTensor dim₁ mult₁ weight₁ A₁) U₁ hReconstruct₁ X]
  rw [hT]
  rw [physClose2_eq_physClose1_blockTwo_apply]
  rw [physClose1_eq_of_vertical_reconstruction (blockTwo M)
    (verticalAssembledTensor dim₂ mult₂ weight₂ A₂) U₂ hReconstruct₂ X]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U₂ U₂ᴴ]
  rw [hU₂]
  simp

/-- The matrix before the final one-site compression lies in the active
one-site sector for every two-site BNT bond contraction.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1980. -/
theorem precompressionVerticalSectorS_image_preservation
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hS : S (physClose2 M X) = physClose1 M X) :
    U₁ᴴ * U₁ * precompressionVerticalSectorS dim₂ mult₂ weight₂ U₂ S
        (fun β => verticalMultiplicityTrace weight₂ β •
          MPSTensor.contractBondMatrix (A₂ β) X) =
      precompressionVerticalSectorS dim₂ mult₂ weight₂ U₂ S
        (fun β => verticalMultiplicityTrace weight₂ β •
          MPSTensor.contractBondMatrix (A₂ β) X) := by
  unfold precompressionVerticalSectorS
  rw [normalizedRetainedVerticalSectorEmbedding_trace_smul
    dim₂ mult₂ weight₂ hMult₂ hWeight₂]
  rw [← contractBondMatrix_verticalAssembledTensor_eq_sectorBlockDiagonal]
  rw [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose]
  rw [← physClose1_eq_of_vertical_reconstruction (blockTwo M)
    (verticalAssembledTensor dim₂ mult₂ weight₂ A₂) U₂ hReconstruct₂ X]
  rw [physClose1_blockTwo_eq_physClose2_apply]
  rw [hS]
  rw [physClose1_eq_of_vertical_reconstruction M
    (verticalAssembledTensor dim₁ mult₁ weight₁ A₁) U₁ hReconstruct₁ X]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U₁ U₁ᴴ]
  rw [hU₁]
  simp

/-- Transported refinement preserves the total sector trace of every
one-site BNT bond contraction.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1980. -/
theorem transportedVerticalSectorT_trace_of_source_generated
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hTTP : IsKrausCPTP T)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hT : T (physClose1 M X) = physClose2 M X) :
    verticalSectorTrace
        (transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T
          (fun α => verticalMultiplicityTrace weight₁ α •
            MPSTensor.contractBondMatrix (A₁ α) X)) =
      verticalSectorTrace
        (fun α => verticalMultiplicityTrace weight₁ α •
          MPSTensor.contractBondMatrix (A₁ α) X) := by
  rw [verticalSectorTrace_transportedVerticalSectorT]
  rw [Matrix.trace_mul_cycle]
  rw [precompressionVerticalSectorT_image_preservation
    dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₁ hWeight₁ M A₁ A₂ U₁ U₂
      hU₂ T hReconstruct₁ hReconstruct₂ X hT]
  exact trace_precompressionVerticalSectorT dim₁ mult₁ weight₁ hMult₁ hWeight₁
    U₁ hU₁ T hTTP _

/-- Transported coarse-graining preserves the total sector trace of every
two-site BNT bond contraction.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1980. -/
theorem transportedVerticalSectorS_trace_of_source_generated
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hSTP : IsKrausCPTP S)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hS : S (physClose2 M X) = physClose1 M X) :
    verticalSectorTrace
        (transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S
          (fun β => verticalMultiplicityTrace weight₂ β •
            MPSTensor.contractBondMatrix (A₂ β) X)) =
      verticalSectorTrace
        (fun β => verticalMultiplicityTrace weight₂ β •
          MPSTensor.contractBondMatrix (A₂ β) X) := by
  rw [verticalSectorTrace_transportedVerticalSectorS]
  rw [Matrix.trace_mul_cycle]
  rw [precompressionVerticalSectorS_image_preservation
    dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₂ hWeight₂ M A₁ A₂ U₁ hU₁
      U₂ S hReconstruct₁ hReconstruct₂ X hS]
  exact trace_precompressionVerticalSectorS dim₂ mult₂ weight₂ hMult₂ hWeight₂
    U₂ hU₂ S hSTP _

end MPOTensor
