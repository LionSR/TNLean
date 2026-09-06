/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceYOneNormalization
import TNLean.MPS.MPU.SourceYTwoNormalization

/-!
# Physical normalizations of the source X factors

The physical closures in arXiv:2502.20257, Proposition `prop:MPUsplus`,
equation `eq:MPUnice4`, follow from the output closure of the physical
adjoint and the source Y normalizations in `eq:MPUnice3`.
-/

open scoped Matrix BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D}

/-- The output-leg version of the one-letter closure, obtained by applying
`eq:MPUnice2` to the physical adjoint. Source: arXiv:2502.20257,
proof of Proposition `prop:MPUsplus`, `eq:MPUnice4`. -/
theorem IsMPUCanonicalFormII.oneLetter_output_contraction
    (hU : IsMPUCanonicalFormII U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U)) (i j : Fin d) :
    (∑ x : Fin D, ∑ α : Fin D, ∑ β : Fin D, ∑ p : Fin d,
      U i p x α * star (U j p x β) * hU.ρ β α) =
        if i = j then 1 else 0 := by
  simpa only [physicalAdjointTensor_apply, star_star,
    IsMPUCanonicalFormII.physicalAdjointTensor] using
    hU.physicalAdjointTensor.oneLetter_physical_contraction hadjoint i j

/-- First physical source X closure: the canonical right boundary remains
between the two virtual legs. Source: arXiv:2502.20257, first diagram of
`eq:MPUnice4` in Proposition `prop:MPUsplus`. -/
theorem IsMPUCanonicalFormII.sourceX₁_physical_contraction
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U)) (i j : Fin d) :
    (∑ r : Fin r[U], ∑ α : Fin D, ∑ β : Fin D,
      sourceX₁ U hU.ρ hU.ρ_posDef (i, α) r * hU.ρ β α *
        star (sourceX₁ U hU.ρ hU.ρ_posDef (j, β) r)) =
      ((r[U] : ℂ) / (d : ℂ)) * (if i = j then 1 else 0) := by
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  have hgram : sourceCutM₁ U * (sourceCutM₁ U)ᴴ =
      ((d : ℂ) / (r[U] : ℂ)) • (S.X₁ * S.X₁ᴴ) := by
    rw [S.sourceCutM₁_eq, Matrix.conjTranspose_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc S.Y₁,
      hU.sourceY₁_mul_conjTranspose hsimple hadjoint]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  have hclosure : (∑ α : Fin D, ∑ β : Fin D,
      (sourceCutM₁ U * (sourceCutM₁ U)ᴴ) (i, α) (j, β) * hU.ρ β α) =
        if i = j then 1 else 0 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      sourceCutM₁_apply, Finset.sum_mul]
    rw [← hU.oneLetter_output_contraction hadjoint i j]
    conv_rhs => rw [Finset.sum_comm]; arg 2; ext α; rw [Finset.sum_comm]
  rw [hgram] at hclosure
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply] at hclosure
  have htrace := hU.trace_sourceY₁_mul_conjTranspose hsimple
  dsimp only at htrace
  rw [hU.sourceY₁_mul_conjTranspose hsimple hadjoint,
    Matrix.trace_smul, Matrix.trace_one] at htrace
  simp only [Fintype.card_fin, smul_eq_mul] at htrace
  have hd : (d : ℂ) ≠ 0 := by
    have := hU.neZero_phys
    exact_mod_cast (NeZero.ne d)
  have hr : (r[U] : ℂ) ≠ 0 := right_ne_zero_of_mul (htrace.trans_ne hd)
  rw [← hclosure]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext α; rw [Finset.sum_comm]
  refine Finset.sum_congr₂ fun α _ β _ ↦ ?_
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  change _ = (r[U] : ℂ) / d * (d / (r[U] : ℂ) *
    (sourceX₁ U hU.ρ hU.ρ_posDef (i, α) r *
      star (sourceX₁ U hU.ρ hU.ρ_posDef (j, β) r)) * hU.ρ β α)
  field_simp

private theorem sourceCutM₂_output_contraction
    (hU : IsMPUCanonicalFormII U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U)) (i j : Fin d) :
    (∑ x : Fin D, (sourceCutM₂ U * sourceWeight (d := d) hU.ρ *
      (sourceCutM₂ U)ᴴ) (x, i) (x, j)) = if i = j then 1 else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    sourceCutM₂_apply, sourceWeight, kroneckerMap_apply, Matrix.one_apply,
    mul_ite, one_mul, mul_zero, Finset.sum_mul,
    ite_mul, zero_mul, Finset.sum_const_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← hU.oneLetter_output_contraction hadjoint i j]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Fintype.sum_reverse_three]
  refine Finset.sum_congr₂ fun α _ β _ ↦ ?_
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hρ : hU.ρ α β = hU.ρ β α :=
    congrArg (fun M : Matrix (Fin D) (Fin D) ℂ ↦ M β α) hU.ρ_isDiag.isSymm.eq
  rw [hρ]
  ring

/-- Second physical source X closure, with the virtual and source-rank legs
closed and the physical legs open. Source: arXiv:2502.20257, second diagram
of `eq:MPUnice4` in Proposition `prop:MPUsplus`. -/
theorem IsMPUCanonicalFormII.sourceX₂_physical_contraction
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U)) (i j : Fin d) :
    (∑ l : Fin ℓ[U], ∑ x : Fin D,
      sourceX₂ U (x, i) l * star (sourceX₂ U (x, j) l)) =
      ((ℓ[U] : ℂ) / (d : ℂ)) * (if i = j then 1 else 0) := by
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  have hgram : sourceCutM₂ U * sourceWeight (d := d) hU.ρ * (sourceCutM₂ U)ᴴ =
      ((d : ℂ) / (ℓ[U] : ℂ)) • (S.X₂ * S.X₂ᴴ) := by
    rw [S.sourceCutM₂_eq, Matrix.conjTranspose_mul]
    calc
      _ = S.X₂ * (S.Y₂ * sourceWeight (d := d) hU.ρ * S.Y₂ᴴ) * S.X₂ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hU.sourceY₂_weighted_mul_conjTranspose hsimple hadjoint]
        simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hclosure := sourceCutM₂_output_contraction hU hadjoint i j
  rw [hgram] at hclosure
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply] at hclosure
  have htrace := hU.trace_sourceY₂_weighted_mul_conjTranspose hsimple
  dsimp only at htrace
  rw [hU.sourceY₂_weighted_mul_conjTranspose hsimple hadjoint,
    Matrix.trace_smul, Matrix.trace_one] at htrace
  simp only [Fintype.card_fin, smul_eq_mul] at htrace
  have hd : (d : ℂ) ≠ 0 := by
    have := hU.neZero_phys
    exact_mod_cast (NeZero.ne d)
  have hl : (ℓ[U] : ℂ) ≠ 0 := right_ne_zero_of_mul (htrace.trans_ne hd)
  rw [← hclosure]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr₂ fun x _ l _ ↦ ?_
  change _ = (ℓ[U] : ℂ) / d * (d / (ℓ[U] : ℂ) *
    (sourceX₂ U (x, i) l * star (sourceX₂ U (x, j) l)))
  field_simp

end MPOTensor
