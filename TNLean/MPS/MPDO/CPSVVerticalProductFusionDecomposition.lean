/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVVerticalProductCornerPositivity
import TNLean.MPS.MPDO.CPSVVerticalProductSpectralFamily
import TNLean.MPS.MPDO.VerticalProductFusionDecomposition

/-!
# Fusion decomposition from literal CPSV canonical form

Literal CPSV canonical form supplies the retained product spectra, positive
active coefficients, and unitary normalizations needed by the form-neutral
fusion-coisometry construction.

## Main result

* `MPOTensor.exists_positiveFusionDecomposition_of_unitaryBlockEquiv_of_cpsvCanonicalForm`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13 and Appendix C.4, lines 2020--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

/-- A one-site/two-site sector comparison under literal CPSV canonical form
determines positive diagonal fusion data and coisometries onto the active
product sectors.

Source: CPSV16, Proposition 4.13, lines 1863--1921, and Appendix C.4,
lines 2001--2029. -/
theorem exists_positiveFusionDecomposition_of_unitaryBlockEquiv_of_cpsvCanonicalForm
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
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (sigma : Fin g₁ ≃ Fin g₂)
    (hDim : ∀ i, dim₁ i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (hLetter : ∀ (i : Fin g₁) (ab : Fin (D * D)),
      A₂ (sigma i) ab =
        (verticalMultiplicityTrace weight₁ i /
          verticalMultiplicityTrace weight₂ (sigma i)) •
        ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (A₁ i ab) *
          (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ))
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) :
    ∃ (chi : DiagonalChiFamily (Fin g₁))
      (U : ∀ α β : Fin g₁,
        Matrix
          ((γ : Fin g₁) × (Fin (chi.dim α β γ) × Fin (dim₁ γ)))
          (Fin (dim₁ α * dim₁ β)) ℂ),
      chi.PosEntries ∧
      (∀ α β, U α β * (U α β)ᴴ = 1) ∧
      (∀ (α β : Fin g₁) (i j : Fin D),
        U α β *
            (mulTensor (verticalBNTMPO (A₁ α))
              (verticalBNTMPO (A₁ β))) i j *
            (U α β)ᴴ =
          Matrix.blockDiagonal' fun γ =>
            chi.matrix α β γ ⊗ₖ verticalBNTMPO (A₁ γ) i j) ∧
      ∀ (α β : Fin g₁) (i j : Fin D),
        (mulTensor (verticalBNTMPO (A₁ α))
          (verticalBNTMPO (A₁ β))) i j =
          (U α β)ᴴ *
            (Matrix.blockDiagonal' fun γ =>
              chi.matrix α β γ ⊗ₖ verticalBNTMPO (A₁ γ) i j) *
            U α β := by
  classical
  obtain ⟨R⟩ := hCanonical.exists_retainedProductSpectralFamily
    dim₁ mult₁ weight₁ A₁ U₁ hU₁ hReconstruct₁ hM
  letI : ∀ γ, NeZero (dim₂ γ) := fun γ ↦
    ⟨(hBNT₂.blocks_dim_pos γ).ne'⟩
  obtain ⟨C⟩ := R.exists_flatBlockedBNTComparison
    M U₁ hU₁ hReconstruct₁ dim₂ A₂ hBNT₂
  have hNormal₂ : ∀ γ, MPSTensor.IsNormalTensor (A₂ γ) := fun γ ↦
    hBNT₂.blocks_normal γ
  have hActivePos : ∀ j, (0 : ℂ) < R.flatCoefficient j * C.phase j := fun j ↦
    C.activeCoefficient_mul_phase_pos_of_cpsvCanonicalForm
      M hCanonical hM U₁ hU₁ hReconstruct₁
      mult₂ hMult₂ weight₂ hWeight₂ U₂ hU₂ hReconstruct₂ hNormal₂ j
  choose omega homega hGram _hQ using fun j ↦
    C.exists_unitaryNormalization_of_cpsvCanonicalForm
      M hCanonical hM U₁ hU₁ hReconstruct₁
      mult₂ hMult₂ weight₂ hWeight₂ U₂ hU₂ hReconstruct₂ hNormal₂ j
  exact R.exists_bntFusionCoisometryFamily C hMult₁ hWeight₁
    mult₂ hMult₂ weight₂ hWeight₂ sigma hDim V hLetter
    hActivePos omega homega hGram

end MPOTensor
