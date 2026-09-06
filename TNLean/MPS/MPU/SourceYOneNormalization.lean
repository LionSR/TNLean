/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AdjointSimpleContraction
import TNLean.MPS.MPU.SourceYPhysicalContractions

/-!
# Normalization of the first source Y factor

The first identity of arXiv:2502.20257, equation `eq:MPUnice3`, follows by
factoring the raw adjoint-simple contraction, cancelling the chosen source
factors, and taking the physical trace (proof, lines 1326–1398).
No additional physical-dimension normalization is inserted.
-/

open scoped Matrix BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D}

/-- Factorization of the raw contraction through the Gram matrix of the exact
chosen first source factor. Source: arXiv:2502.20257, lines 1326–1374. -/
theorem IsMPUCanonicalFormII.sourceCutM₁_adjointSimpleContraction
    (hU : IsMPUCanonicalFormII U) :
    let S := sourceFactors U hU.ρ hU.ρ_posDef
    sourceCutM₁ (adjointSimpleContraction U hU.ρ) = S.X₁ * (S.Y₁ * S.Y₁ᴴ) * S.Y₁ := by
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  have hW : (sourceWeight (d := d) hU.ρ)ᵀ = sourceWeight (d := d) hU.ρ := by
    rw [sourceWeight, ← Matrix.kroneckerMap_transpose, Matrix.transpose_one,
      hU.ρ_isDiag.isSymm.eq]
  rw [sourceCutM₁_adjointSimpleContraction_raw, S.sourceCutM₁_eq, hW]
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (sourceWeight (d := d) hU.ρ) S.X₁ S.Y₁,
    ← Matrix.mul_assoc S.X₁ᴴ (sourceWeight (d := d) hU.ρ * S.X₁) S.Y₁]
  have hX : S.X₁ᴴ * (sourceWeight (d := d) hU.ρ * S.X₁) = 1 := by
    simpa only [Matrix.mul_assoc] using S.X₁_weighted_isometry
  rw [hX]
  simp only [Matrix.one_mul]
  change S.X₁ * (S.Y₁ * (S.Y₁ᴴ * S.Y₁)) = S.X₁ * (S.Y₁ * (S.Y₁ᴴ * S.Y₁))
  rfl

/-- The source-rank Gram matrix of the first chosen source factor is scalar.
The weighted left inverse and the supplied right inverse cancel the dressing.
Source: arXiv:2502.20257, proof of `eq:MPUnice3`, lines 1375–1397. -/
theorem IsMPUCanonicalFormII.sourceY₁_mul_conjTranspose_eq_smul
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U)) :
    ∃ δ : ℂ, let S := sourceFactors U hU.ρ hU.ρ_posDef
      S.Y₁ * S.Y₁ᴴ = δ • 1 := by
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  obtain ⟨δ, hδ⟩ := hU.adjointSimpleContraction_eq_smul hsimple hadjoint
  refine ⟨δ, ?_⟩
  have hcut : sourceCutM₁ (adjointSimpleContraction U hU.ρ) =
      δ • sourceCutM₁ U := by
    ext ⟨i, b⟩ ⟨a, j⟩
    exact congrArg (fun M ↦ M a b) (hδ i j)
  rw [hU.sourceCutM₁_adjointSimpleContraction, S.sourceCutM₁_eq] at hcut
  change S.X₁ * (S.Y₁ * S.Y₁ᴴ) * S.Y₁ = δ • (S.X₁ * S.Y₁) at hcut
  have hcancel := congrArg (fun M ↦
    (S.X₁ᴴ * sourceWeight (d := d) hU.ρ) * M * S.Z₁) hcut
  change S.Y₁ * S.Y₁ᴴ = δ • 1
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc,
    S.X₁_weighted_isometry, Matrix.one_mul] at hcancel
  simpa only [Matrix.mul_assoc, S.Y₁_mul_Z₁, Matrix.mul_one] using hcancel

/-- The physical closure fixes the full trace of the first source Gram matrix.
Source: arXiv:2502.20257, equations `eq:MPUnice2` and `eq:MPUnice3`. -/
theorem IsMPUCanonicalFormII.trace_sourceY₁_mul_conjTranspose
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U) :
    let S := sourceFactors U hU.ρ hU.ρ_posDef
    (S.Y₁ * S.Y₁ᴴ).trace = (d : ℂ) := by
  change (sourceY₁ U hU.ρ hU.ρ_posDef *
    (sourceY₁ U hU.ρ hU.ρ_posDef)ᴴ).trace = _
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
  simp_rw [hU.sourceY₁_physical_contraction hsimple]
  simp

/-- First source-factor constant, with the exact chosen factors and no extra
normalization: $Y_1Y_1^\dagger=(d/r)I$.
Source: arXiv:2502.20257, first identity of `eq:MPUnice3`, proof lines 1326–1398. -/
theorem IsMPUCanonicalFormII.sourceY₁_mul_conjTranspose
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U)) :
    let S := sourceFactors U hU.ρ hU.ρ_posDef
    S.Y₁ * S.Y₁ᴴ = ((d : ℂ) / (r[U] : ℂ)) • 1 := by
  obtain ⟨δ, hδ⟩ := hU.sourceY₁_mul_conjTranspose_eq_smul hsimple hadjoint
  have htrace := hU.trace_sourceY₁_mul_conjTranspose hsimple
  dsimp only at hδ htrace ⊢
  rw [hδ, Matrix.trace_smul, Matrix.trace_one] at htrace
  simp only [Fintype.card_fin, smul_eq_mul] at htrace
  have hd : (d : ℂ) ≠ 0 := by
    have := hU.neZero_phys
    exact_mod_cast (NeZero.ne d)
  have hr : (r[U] : ℂ) ≠ 0 := right_ne_zero_of_mul (htrace.trans_ne hd)
  have hscalar : δ = (d : ℂ) / (r[U] : ℂ) := (eq_div_iff hr).mpr htrace
  simpa only [hscalar] using hδ

end MPOTensor
