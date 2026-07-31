/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVBlocking
import TNLean.MPS.MPDO.CPSVFigureEight
import TNLean.MPS.MPDO.CPSVVerticalBNT
import TNLean.MPS.MPDO.VerticalProductCornerPositivity

/-!
# Literal CPSV positivity and normalization of active product gauges

The literal CPSV canonical form supplies the sector-compression separation
and Figure 8 Gram comparison needed to normalize the active product corners
in the RFP-to-fusion construction.

## Main results

* `FlatBlockedBNTComparison.activeCoefficient_mul_phase_pos_of_cpsvCanonicalForm`:
  every active product coefficient is positive.
* `FlatBlockedBNTComparison.exists_unitaryNormalization_of_cpsvCanonicalForm`:
  every active product gauge has positive scalar Gram matrix and can be
  normalized to a unitary.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, lines 1898--1921, and Appendix C.4, lines 2020--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

namespace RetainedProductSpectralFamily

variable {g D : ℕ} {dim mult : Fin g → ℕ}
  {weight : (α : Fin g) → Fin (mult α) → ℂ}
  {B : (α : Fin g) → MPSTensor (D * D) (dim α)}

/-- The scalar multiplying every active product corner is positive under
literal CPSV canonical form.

Source: CPSV16, Proposition 4.13, lines 1898--1902, and Appendix C.4,
lines 2025--2029. -/
theorem FlatBlockedBNTComparison.activeCoefficient_mul_phase_pos_of_cpsvCanonicalForm
    {g₂ d : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    {S : RetainedProductSpectralFamily dim mult weight B}
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim mult weight B ab * U₁)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (hWeight₂ : ∀ γ q, (0 : ℂ) < weight₂ γ q)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g₂, mult₂ γ),
        verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (hNormal₂ : ∀ γ, MPSTensor.IsNormalTensor (A₂ γ))
    (j : Fin (Fintype.card S.ActiveLabel)) :
    (0 : ℂ) < S.flatCoefficient j * C.phase j := by
  let hBlocked := IsCPSVCanonicalForm_toMPSTensor_blockTwo hCanonical
  refine C.activeCoefficient_mul_phase_pos_of_sectorCompression_separation M hM
    ?_ (U₁ := U₁) hU₁ hReconstruct₁ mult₂ hMult₂ weight₂ hWeight₂
      U₂ hU₂ hReconstruct₂ hNormal₂ j
  intro P hP
  exact hBlocked.exists_sectorCompression_ne_zero_of_corner
    (blockTwo M) P hP

/-- Every active product gauge has positive scalar Gram matrix and becomes
unitary after division by the square root of that scalar under literal CPSV
canonical form.

Source: CPSV16, Proposition 4.13, lines 1903--1921, and Appendix C.4,
lines 2025--2029. -/
theorem FlatBlockedBNTComparison.exists_unitaryNormalization_of_cpsvCanonicalForm
    {g₂ d : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    {S : RetainedProductSpectralFamily dim mult weight B}
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim mult weight B ab * U₁)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (hWeight₂ : ∀ γ q, (0 : ℂ) < weight₂ γ q)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g₂, mult₂ γ),
        verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (hNormal₂ : ∀ γ, MPSTensor.IsNormalTensor (A₂ γ))
    (j : Fin (Fintype.card S.ActiveLabel)) :
    ∃ ω : ℝ, 0 < ω ∧
      (C.gauge j : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ)ᴴ *
          C.gauge j = (ω : ℂ) • 1 ∧
      ((Real.sqrt ω : ℂ))⁻¹ •
          (C.gauge j : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ) ∈
        Matrix.unitaryGroup (Fin (S.flatDim j)) ℂ := by
  let hBlocked := IsCPSVCanonicalForm_toMPSTensor_blockTwo hCanonical
  let x := S.activeLabelEquiv j
  let A := cast (congrArg (MPSTensor (D * D)) (C.dim_eq j))
    (A₂ (C.label j))
  let Vact := S.ambientInclusion U₁ x
  let Vref := C.referenceInclusion mult₂ hMult₂ U₂ j
  let c := S.flatCoefficient j * C.phase j
  let c₀ := weight₂ (C.label j) ⟨0, hMult₂ (C.label j)⟩
  letI : NeZero (S.flatDim j) := ⟨(S.flatDim_pos j).ne'⟩
  have hA : MPSTensor.IsNormalTensor A :=
    (MPSTensor.isNormalTensor_cast_iff (C.dim_eq j) (A₂ (C.label j))).2
      (hNormal₂ (C.label j))
  have hc : (0 : ℂ) < c :=
    C.activeCoefficient_mul_phase_pos_of_cpsvCanonicalForm M hCanonical hM
      U₁ hU₁ hReconstruct₁ mult₂ hMult₂ weight₂ hWeight₂ U₂ hU₂
      hReconstruct₂ hNormal₂ j
  have hc₀ : (0 : ℂ) < c₀ :=
    hWeight₂ (C.label j) ⟨0, hMult₂ (C.label j)⟩
  have hActiveCorner : ∀ ab,
      Vactᴴ * verticalTensor (blockTwo M) ab * Vact =
        c • ((C.gauge j : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ) * A ab *
          (↑((C.gauge j)⁻¹) : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ)) := by
    intro ab
    symm
    calc
      c • ((C.gauge j : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ) * A ab *
          (↑((C.gauge j)⁻¹) : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ)) =
        S.flatCoefficient j • S.flatBlock j ab := by
          rw [C.block_eq j ab]
          simp only [c, A, smul_smul]
      _ = Vactᴴ * verticalTensor (blockTwo M) ab * Vact := by
        change S.coefficient x.1 x.2 • S.block x.1 x.2 ab = _
        exact S.ambient_compression M U₁ hU₁ hReconstruct₁ x ab
  have hReferenceCorner : ∀ ab,
      Vrefᴴ * verticalTensor (blockTwo M) ab * Vref = c₀ • A ab := by
    intro ab
    exact (C.reference_compression M mult₂ hMult₂ weight₂ U₂ hU₂
      hReconstruct₂ j ab).symm
  obtain ⟨ω, hω, hGram⟩ :=
    hBlocked.gram_eq_pos_smul_gram_of_two_grouped_corners
      (blockTwo M) hM.blockTwo A hA.isNormal Vact Vref (C.gauge j) 1
      c c₀ hc hc₀ hActiveCorner (by
        intro ab
        simpa using hReferenceCorner ab)
  have hGramOne :
      (C.gauge j : Matrix (Fin (S.flatDim j))
          (Fin (S.flatDim j)) ℂ)ᴴ * C.gauge j = (ω : ℂ) • 1 := by
    simpa using hGram
  exact ⟨ω, hω, hGramOne,
    Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one
      hω hGramOne⟩

end RetainedProductSpectralFamily

end MPOTensor
