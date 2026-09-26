/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.AnomalousCondensation.AnomalousCondensationZ2Z2Unitary

/-!
# Anomalous `ℤ/2 × ℤ/2` symmetry: the adjoint of the condensation defect

**Source.** Construction of this development; no source prints these tensors.
The term *condensation defect* for the sum of the operators of a finite symmetry follows
Roumpedakis, Seifnashri and Shao (arXiv:2204.02407), Section "Higher gauging and condensation
defects", `References/2204.02407/source/condensation_draft.tex` lines 145–148; lines 1415–1417
of the same file note that for an anomaly-free `ℤ/2` operator `U` the sum `P_+ = 1 + U` obeys
`P_+ × P_+ = 2 P_+`, so `P_+ / 2` is an orthogonal projector.

**Formalized here.** For the condensation defect `A_L = U_e + U_x + U_y + U_xy` of the
anomalous `ℤ/2 × ℤ/2` symmetry, the adjoint is
`A_L^† = 1 + U_{x,L} + U_{y,L} + (-1)^L U_{xy,L}`. On every positive even ring `A_L / 4` is an
orthogonal projector (a self-adjoint idempotent). On every odd ring `A_L / 2` is idempotent but
not self-adjoint, since `A_L^† - A_L = -2 U_{xy,L}` and `U_{xy,L}` is unitary.

## Main results

* `Z2Z2Condensation.mpo_condensationTensor_conjTranspose`: the adjoint formula.
* `Z2Z2Condensation.isStarProjection_quarter_condensation_of_even`: `A_L / 4` is an
  orthogonal projector on even rings.
* `Z2Z2Condensation.isIdempotentElem_half_condensation_of_odd`,
  `Z2Z2Condensation.conjTranspose_sub_mpo_condensationTensor_of_odd`,
  `Z2Z2Condensation.not_isSelfAdjoint_half_condensation_of_odd`: on odd rings `A_L / 2` is an
  idempotent that is not self-adjoint.

## References

- [arXiv:2204.02407](https://arxiv.org/abs/2204.02407) -- K. Roumpedakis, S. Seifnashri,
  S.-H. Shao, *Higher Gauging and Non-invertible Condensation Defects*
-/

noncomputable section

open scoped Matrix

namespace Z2Z2Condensation

open MPSTensor MPOTensor

/-- **The adjoint of the condensation defect**:
`A_L^† = 1 + U_{x,L} + U_{y,L} + (-1)^L U_{xy,L}`. The identity, `U_x` and `U_y` are
self-adjoint, while `U_{xy,L}^† = (-1)^L U_{xy,L}`. -/
theorem mpo_condensationTensor_conjTranspose (L : ℕ) (hL : 0 < L) :
    (mpo condensationTensor L)ᴴ =
      1 + mpo xTensor L + mpo yTensor L + (-1 : ℂ) ^ L • mpo xyTensor L := by
  have : NeZero L := ⟨hL.ne'⟩
  have he : (mpo eTensor L)ᴴ = 1 := by
    rw [show mpo eTensor L = mpo (symTensor 0) L from rfl, mpo_symTensor_zero,
      Matrix.conjTranspose_one]
  have hx : (mpo xTensor L)ᴴ = mpo xTensor L := by
    have h := mpo_symTensor_conjTranspose (N := L) 2
    simp only [fusionSign, one_pow, one_smul] at h
    exact h
  have hy : (mpo yTensor L)ᴴ = mpo yTensor L := by
    have h := mpo_symTensor_conjTranspose (N := L) 1
    simp only [fusionSign, one_pow, one_smul] at h
    exact h
  have hxy : (mpo xyTensor L)ᴴ = (-1 : ℂ) ^ L • mpo xyTensor L := by
    exact mpo_symTensor_conjTranspose (N := L) 3
  rw [mpo_condensationTensor]
  simp only [Matrix.conjTranspose_add, he, hx, hy, hxy]

/-- The diagonal group operator `U_{xy,L}` is nonzero on every positive ring, being unitary. -/
theorem mpo_xyTensor_ne_zero (L : ℕ) (hL : 0 < L) : mpo xyTensor L ≠ 0 := by
  have : NeZero L := ⟨hL.ne'⟩
  intro h
  have hu := Matrix.mem_unitaryGroup_iff.mp (mpo_symTensor_mem_unitaryGroup (N := L) 3)
  change mpo xyTensor L * star (mpo xyTensor L) = 1 at hu
  rw [h, zero_mul] at hu
  exact zero_ne_one hu

/-- **On every positive even ring `A_L / 4` is an orthogonal projector**: it is idempotent
(`condensation_quarter_sq_eq_self_iff_even`) and self-adjoint, since the adjoint formula
returns `A_L` when `(-1)^L = 1`. -/
theorem isStarProjection_quarter_condensation_of_even {L : ℕ} (hL : 0 < L) (he : Even L) :
    IsStarProjection ((4 : ℂ)⁻¹ • mpo condensationTensor L) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, ← sq]
    exact (condensation_quarter_sq_eq_self_iff_even L hL).2 he
  · have hA : (mpo condensationTensor L)ᴴ = mpo condensationTensor L := by
      rw [mpo_condensationTensor_conjTranspose L hL, he.neg_one_pow, one_smul,
        mpo_condensationTensor]
      rw [show mpo eTensor L = mpo (symTensor 0) L from rfl]
      have : NeZero L := ⟨hL.ne'⟩
      rw [mpo_symTensor_zero]
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, hA]
    congr 1
    simp

/-- **On every odd ring `A_L / 2` is idempotent**: the square identity
`A_L² = (3 + (-1)^L) A_L` reads `A_L² = 2 A_L` for odd `L`. -/
theorem isIdempotentElem_half_condensation_of_odd {L : ℕ} (ho : Odd L) :
    IsIdempotentElem ((2 : ℂ)⁻¹ • mpo condensationTensor L) := by
  rw [IsIdempotentElem, ← sq, smul_pow, mpo_condensationTensor_sq L ho.pos, ho.neg_one_pow,
    smul_smul]
  congr 1
  norm_num

/-- **On every odd ring `A_L^† - A_L = -2 U_{xy,L}`.** -/
theorem conjTranspose_sub_mpo_condensationTensor_of_odd {L : ℕ} (ho : Odd L) :
    (mpo condensationTensor L)ᴴ - mpo condensationTensor L = (-2 : ℂ) • mpo xyTensor L := by
  rw [mpo_condensationTensor_conjTranspose L ho.pos, ho.neg_one_pow, mpo_condensationTensor,
    show mpo eTensor L = mpo (symTensor 0) L from rfl]
  have : NeZero L := ⟨ho.pos.ne'⟩
  rw [mpo_symTensor_zero]
  module

/-- **On every odd ring `A_L / 2` is not self-adjoint**, because
`A_L^† - A_L = -2 U_{xy,L}` is nonzero. -/
theorem not_isSelfAdjoint_half_condensation_of_odd {L : ℕ} (ho : Odd L) :
    ¬ IsSelfAdjoint ((2 : ℂ)⁻¹ • mpo condensationTensor L) := by
  intro h
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul] at h
  have h2 : star (2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by simp
  rw [h2] at h
  have hA : (mpo condensationTensor L)ᴴ = mpo condensationTensor L :=
    smul_right_injective _ (by norm_num : (2 : ℂ)⁻¹ ≠ 0) h
  have hsub := conjTranspose_sub_mpo_condensationTensor_of_odd ho
  rw [hA, sub_self] at hsub
  exact mpo_xyTensor_ne_zero L ho.pos
    ((smul_eq_zero.mp hsub.symm).resolve_left (by norm_num))

end Z2Z2Condensation
