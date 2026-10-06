/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.SemiRegularBondSparseAction
import TNLean.PEPS.SemiRegularBondProductIsometry

/-!
# Retractions of products of supported multiplicity maps

Multiplicity restoration and its adjoint are inverse on the matching-sector
input space and on the actual output image, respectively. These identities
hold for arbitrary vectors in the product supports, and hence apply to full
canonical parent kernels once their supports have been derived locally.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2992–3019.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (ν μ : I → Type*) [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)]
variable [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)] [∀ i, Nonempty (μ i)]

/-- The supported endpoint map is a partial isometry on its full ambient spaces. -/
theorem fullMultiplicityBondMap_mul_adjoint_mul :
    fullMultiplicityBondMap ν μ * (fullMultiplicityBondMap ν μ).conjTranspose *
      fullMultiplicityBondMap ν μ = fullMultiplicityBondMap ν μ := by
  rw [Matrix.mul_assoc, fullMultiplicityBondMap_initialProjection]
  have hE := blockBondInclusion_isIsometry ν
  calc
    _ = blockBondInclusion (fun i => ν i × μ i) * multiplicityBlockBondMatrix ν μ *
        ((blockBondInclusion ν).conjTranspose * blockBondInclusion ν) *
        (blockBondInclusion ν).conjTranspose := by
      simp only [fullMultiplicityBondMap, Matrix.mul_assoc]
    _ = _ := by rw [hE, Matrix.mul_one]; rfl

variable (E : Type*) [Fintype E] [DecidableEq E]

/-- The product adjoint is a left inverse on the complete product matching-sector support. -/
theorem physicalProductMap_fullMultiplicityBondMap_leftInverse
    {ψ : (E → ((Σ i, ν i) × (Σ i, ν i))) → ℂ}
    (hψ : ψ ∈ LinearMap.range (physicalProductMap E (blockBondInclusion ν))) :
    physicalProductMap E (fullMultiplicityBondMap ν μ).conjTranspose
      (physicalProductMap E (fullMultiplicityBondMap ν μ) ψ) = ψ := by
  obtain ⟨χ, rfl⟩ := hψ
  simp only [physicalProductMap, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    physicalProductMatrix_mul, physicalProductMatrix_mul,
    fullMultiplicityBondMap_initialProjection, Matrix.mul_assoc,
    blockBondInclusion_isIsometry, Matrix.mul_one]

/-- The product map is a right inverse of its adjoint on its entire output image. -/
theorem physicalProductMap_fullMultiplicityBondMap_rightInverse
    {ψ : (E → ((Σ i, ν i × μ i) × (Σ i, ν i × μ i))) → ℂ}
    (hψ : ψ ∈ LinearMap.range (physicalProductMap E (fullMultiplicityBondMap ν μ))) :
    physicalProductMap E (fullMultiplicityBondMap ν μ)
      (physicalProductMap E (fullMultiplicityBondMap ν μ).conjTranspose ψ) = ψ := by
  obtain ⟨χ, rfl⟩ := hψ
  simp only [physicalProductMap, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    physicalProductMatrix_mul, physicalProductMatrix_mul,
    fullMultiplicityBondMap_mul_adjoint_mul]

end TNLean.PEPS
