/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AdjointSimpleContraction
import TNLean.MPS.MPU.SourceYPhysicalContractions

/-!
# Normalization of the second source Y factor

The second identity of arXiv:2502.20257, Proposition `prop:MPUsplus`,
`eq:MPUnice3`, is proved for the exact chosen source factors. Apply the raw
contraction to the physical adjoint, cancel the second source factors, and
use their physical closure to determine the scalar. No identification of
chosen singular vectors for the adjoint is needed.
-/

open scoped Matrix BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D}

-- The transpose records the raw contraction's boundary entry `ρ t r`.
private theorem sourceCutM₁_adjointSimpleContraction_raw (T : MPOTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) :
    sourceCutM₁ (adjointSimpleContraction T ρ) =
      sourceCutM₁ T * (sourceCutM₁ T)ᴴ * (sourceWeight (d := d) ρ)ᵀ *
        sourceCutM₁ T := by
  ext ⟨i, b⟩ ⟨a, j⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, sourceWeight, kroneckerMap_apply, Matrix.one_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_mul, Finset.mul_sum,
    sourceCutM₁_apply, adjointSimpleContraction]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  conv_rhs =>
    rw [Fintype.sum_last_two_first_five, Finset.sum_comm]
    arg 2; ext p
    arg 2; ext x
    rw [Fintype.sum_reverse_three]
  congr 1
  ext p
  refine Finset.sum_congr₂ fun x _ r _ ↦ ?_
  refine Finset.sum_congr₂ fun t _ q _ ↦ ?_
  ring

/-- The adjoint raw contraction factors through the weighted Gram matrix of
our chosen second source factor. Source: arXiv:2502.20257, proof of
Proposition `prop:MPUsplus`, second identity of `eq:MPUnice3`. -/
theorem IsMPUCanonicalFormII.sourceCutM₁_adjointSimpleContraction_physicalAdjoint
    (hU : IsMPUCanonicalFormII U) :
    let S := sourceFactors U hU.ρ hU.ρ_posDef
    sourceCutM₁ (adjointSimpleContraction (MPOTensor.physicalAdjointTensor U) hU.ρ) =
      S.Y₂ᴴ * (S.Y₂ * sourceWeight (d := d) hU.ρ * S.Y₂ᴴ) * S.X₂ᴴ := by
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  have hW : (sourceWeight (d := d) hU.ρ)ᵀ = sourceWeight (d := d) hU.ρ := by
    rw [sourceWeight, ← Matrix.kroneckerMap_transpose, Matrix.transpose_one,
      hU.ρ_isDiag.isSymm.eq]
  rw [sourceCutM₁_adjointSimpleContraction_raw, sourceCutM₁_physicalAdjointTensor,
    S.sourceCutM₂_eq, hW]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  change S.Y₂ᴴ * S.X₂ᴴ * (S.X₂ * S.Y₂) * sourceWeight hU.ρ *
    (S.Y₂ᴴ * S.X₂ᴴ) = _
  have hX : S.X₂ᴴ * S.X₂ = 1 := S.X₂_isometry
  simp only [Matrix.mul_assoc] at ⊢
  rw [← Matrix.mul_assoc S.X₂ᴴ S.X₂, hX, Matrix.one_mul]

/-- The weighted source-rank Gram matrix of the second chosen factor is scalar.
Source: arXiv:2502.20257, proof of Proposition `prop:MPUsplus`, `eq:MPUnice3`.
The scalar is obtained from the adjoint tensor, not from the first factor of `U`. -/
theorem IsMPUCanonicalFormII.sourceY₂_weighted_mul_conjTranspose_eq_smul
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U)) :
    ∃ ε : ℂ, let S := sourceFactors U hU.ρ hU.ρ_posDef
      S.Y₂ * sourceWeight (d := d) hU.ρ * S.Y₂ᴴ = ε • 1 := by
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  obtain ⟨ε, hε⟩ := hU.physicalAdjointTensor.adjointSimpleContraction_eq_smul hadjoint
    (by simpa only [physicalAdjointTensor_physicalAdjointTensor] using hsimple)
  refine ⟨ε, ?_⟩
  have hcut : sourceCutM₁ (adjointSimpleContraction
      (MPOTensor.physicalAdjointTensor U) hU.ρ) =
      ε • sourceCutM₁ (MPOTensor.physicalAdjointTensor U) := by
    ext ⟨i, b⟩ ⟨a, j⟩
    exact congrArg (fun M ↦ M a b) (hε i j)
  rw [hU.sourceCutM₁_adjointSimpleContraction_physicalAdjoint,
    sourceCutM₁_physicalAdjointTensor, S.sourceCutM₂_eq, Matrix.conjTranspose_mul] at hcut
  change S.Y₂ᴴ * (S.Y₂ * sourceWeight hU.ρ * S.Y₂ᴴ) * S.X₂ᴴ =
    ε • (S.Y₂ᴴ * S.X₂ᴴ) at hcut
  have hcancel := congrArg (fun M ↦ S.Z₂ᴴ * M * S.X₂) hcut
  have hZ : S.Z₂ᴴ * S.Y₂ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, S.Y₂_mul_Z₂, Matrix.conjTranspose_one]
  have hX : S.X₂ᴴ * S.X₂ = 1 := S.X₂_isometry
  change S.Y₂ * sourceWeight hU.ρ * S.Y₂ᴴ = ε • 1
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hZ,
    Matrix.one_mul] at hcancel
  simpa only [Matrix.mul_assoc, hX, Matrix.mul_one] using hcancel

/-- Physical closure fixes the trace of the weighted second source Gram matrix.
Source: arXiv:2502.20257, `eq:MPUnice2` and second identity of `eq:MPUnice3`. -/
theorem IsMPUCanonicalFormII.trace_sourceY₂_weighted_mul_conjTranspose
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U) :
    let S := sourceFactors U hU.ρ hU.ρ_posDef
    (S.Y₂ * sourceWeight (d := d) hU.ρ * S.Y₂ᴴ).trace = (d : ℂ) := by
  change (sourceY₂ U * sourceWeight (d := d) hU.ρ * (sourceY₂ U)ᴴ).trace = _
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, sourceWeight, kroneckerMap_apply, Matrix.one_apply,
    ite_mul, one_mul, zero_mul, Finset.mul_sum, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ← mul_assoc]
  conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
  simp_rw [hU.sourceY₂_physical_contraction hsimple]
  simp

/-- Second source-factor constant for the exact chosen factors:
$Y_2 (I_d \otimes \rho) Y_2^\dagger=(d/\ell)I$.
Source: arXiv:2502.20257, Proposition `prop:MPUsplus`, second identity of `eq:MPUnice3`.
Nonzero source rank follows from the trace equation, with no extra hypothesis. -/
theorem IsMPUCanonicalFormII.sourceY₂_weighted_mul_conjTranspose
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U)) :
    let S := sourceFactors U hU.ρ hU.ρ_posDef
    S.Y₂ * sourceWeight (d := d) hU.ρ * S.Y₂ᴴ = ((d : ℂ) / (ℓ[U] : ℂ)) • 1 := by
  obtain ⟨ε, hε⟩ := hU.sourceY₂_weighted_mul_conjTranspose_eq_smul hsimple hadjoint
  have htrace := hU.trace_sourceY₂_weighted_mul_conjTranspose hsimple
  dsimp only at hε htrace ⊢
  rw [hε, Matrix.trace_smul, Matrix.trace_one] at htrace
  simp only [Fintype.card_fin, smul_eq_mul] at htrace
  have hd : (d : ℂ) ≠ 0 := by
    have := hU.neZero_phys
    exact_mod_cast (NeZero.ne d)
  have hl : (ℓ[U] : ℂ) ≠ 0 := right_ne_zero_of_mul (htrace.trans_ne hd)
  have hscalar : ε = (d : ℂ) / (ℓ[U] : ℂ) := (eq_div_iff hl).mpr htrace
  simpa only [hscalar] using hε

end MPOTensor
