/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FrobeniusHilbert
import TNLean.Algebra.RectangularChoi
import TNLean.Channel.Primitive

/-!
# The limiting Gram metric

This file computes the reshuffled Choi matrix of the rank-one transfer
fixed-point projection. With column vectorization
`Matrix.vec X (j, i) = X i j`, the resulting unweighted Frobenius Gram operator
is right multiplication by the fixed point, divided by its trace.

## Main results

* `Matrix.gramReshuffleMatrix_fixedPointProj_apply` gives the four-index entry formula.
* `Matrix.gramReshuffleMatrix_fixedPointProj` identifies the Kronecker-product matrix.
* `Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply` computes its action.
* `Matrix.gramReshuffleMatrix_fixedPointProj_posDef` proves positive definiteness.
* `Matrix.gramReshuffle_fixedPointProj_isUnit` proves invertibility.
* `Matrix.gramReshuffle_fixedPointProj_injective` proves injectivity.
* `Matrix.inverse_gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply`
  computes the inverse action.
-/

open scoped ComplexOrder Kronecker Matrix Matrix.Norms.Frobenius

namespace Matrix

variable {D : ℕ}

/-- Entries of the limiting Gram matrix in column-vectorized coordinates. -/
@[simp]
theorem gramReshuffleMatrix_fixedPointProj_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : trace ρ ≠ 0)
    (a b c e : Fin D) :
    gramReshuffleMatrix (fixedPointProj ρ htr) (b, a) (e, c) =
      (trace ρ)⁻¹ * ρ e b * if c = a then 1 else 0 := by
  rw [gramReshuffleMatrix, rectangularChoi_apply]
  change ((trace (single c a 1) / trace ρ) • ρ) e b = _
  by_cases hca : c = a
  · subst c
    simp [Matrix.trace_single_eq_same, div_eq_mul_inv]
  · simp [Matrix.trace_single_eq_of_ne c a (1 : ℂ) hca, hca]

/-- The limiting Gram matrix is a Kronecker product of the transposed fixed
point with the identity, with normalization by the trace. -/
theorem gramReshuffleMatrix_fixedPointProj
    (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : trace ρ ≠ 0) :
    gramReshuffleMatrix (fixedPointProj ρ htr) =
      (trace ρ)⁻¹ • ((ρᵀ) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
  ext ⟨b, a⟩ ⟨e, c⟩
  rw [gramReshuffleMatrix_fixedPointProj_apply]
  change (trace ρ)⁻¹ * ρ e b * (if c = a then 1 else 0) =
    (trace ρ)⁻¹ * (ρ e b * if a = c then 1 else 0)
  by_cases hca : c = a
  · subst c
    simp
  · simp [hca, Ne.symm hca]

/-- In column-vectorized Frobenius coordinates, the limiting Gram operator is
right multiplication by the fixed point, normalized by its trace. -/
theorem gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : trace ρ ≠ 0)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    gramReshuffle (fixedPointProj ρ htr)
        (frobeniusEquivEuclidean (Fin D) (Fin D) X) =
      frobeniusEquivEuclidean (Fin D) (Fin D) ((trace ρ)⁻¹ • (X * ρ)) := by
  rw [gramReshuffle, gramReshuffleMatrix_fixedPointProj,
    frobeniusEquivEuclidean_apply, Matrix.toEuclideanCLM_toLp]
  congr 1
  rw [Matrix.smul_mulVec, Matrix.kronecker_mulVec_vec,
    Matrix.transpose_transpose, Matrix.one_mul, Matrix.vec_smul]

/-- A positive-definite fixed point induces a positive-definite limiting Gram
matrix. -/
theorem gramReshuffleMatrix_fixedPointProj_posDef [NeZero D]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) :
    (gramReshuffleMatrix
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))).PosDef := by
  rw [gramReshuffleMatrix_fixedPointProj]
  exact (hρ.transpose.kronecker PosDef.one).smul (inv_pos.mpr hρ.trace_pos)

/-- A positive-definite fixed point makes the limiting Gram operator invertible. -/
theorem gramReshuffle_fixedPointProj_isUnit [NeZero D]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) :
    IsUnit (gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))) := by
  rw [gramReshuffle]
  exact (gramReshuffleMatrix_fixedPointProj_posDef hρ).isUnit.map
    (Matrix.toEuclideanCLM (n := Fin D × Fin D) (𝕜 := ℂ))

/-- A positive-definite fixed point makes the limiting Gram operator injective. -/
theorem gramReshuffle_fixedPointProj_injective [NeZero D]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) :
    Function.Injective
      (gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))) := by
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp
    (gramReshuffle_fixedPointProj_isUnit hρ)).1

/-- The inverse limiting Gram operator is right multiplication by the
nonsingular inverse of the fixed point, with the reciprocal normalization
cancelled. -/
theorem inverse_gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply [NeZero D]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Ring.inverse (gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))
        (frobeniusEquivEuclidean (Fin D) (Fin D) X) =
      frobeniusEquivEuclidean (Fin D) (Fin D)
        ((trace ρ) • (X * ρ⁻¹)) := by
  let K := gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  have hK : IsUnit K := gramReshuffle_fixedPointProj_isUnit hρ
  apply gramReshuffle_fixedPointProj_injective hρ
  change K (Ring.inverse K (frobeniusEquivEuclidean (Fin D) (Fin D) X)) =
    K (frobeniusEquivEuclidean (Fin D) (Fin D) ((trace ρ) • (X * ρ⁻¹)))
  rw [← ContinuousLinearMap.comp_apply]
  have hcancel : K.comp (Ring.inverse K) = 1 :=
    Ring.isUnit_iff_mul_inverse_cancel.mp hK
  rw [hcancel]
  rw [gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply]
  change frobeniusEquivEuclidean (Fin D) (Fin D) X =
    frobeniusEquivEuclidean (Fin D) (Fin D)
      ((trace ρ)⁻¹ • ((trace ρ) • (X * ρ⁻¹) * ρ))
  congr 1
  rw [Matrix.smul_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul ρ (ρ.isUnit_iff_isUnit_det.mp hρ.isUnit),
    Matrix.mul_one, smul_smul, inv_mul_cancel₀ (ne_of_gt hρ.trace_pos), one_smul]


end Matrix
