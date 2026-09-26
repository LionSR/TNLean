/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ReducedRepresentative
import TNLean.MPS.MPU.TransferMatrix

/-!
# Normalized transfer maps under virtual compression

The transfer map in the MPU paper is that of the normalized flattening,
not the unnormalized MPO transfer map. Virtual sandwiching commutes with this
normalization. Consequently, compressing a supplied positive fixed pair does
not introduce a factor of the physical dimension.

**Scope restriction (supplied fixed pair):**
`transferMap_normalizedFlattening_reducedProjection` assumes the fixed pair.
Its construction after blocking an arbitrary MPU is a separate step; see
`docs/paper-gaps/mpu_reduced_representative_supplied_fixed_pair.tex`.

## Main results

* `MPOTensor.transferMap_normalizedFlattening_virtualSandwich` gives the
  normalized transfer map under arbitrary virtual sandwiching.
* `MPOTensor.transferMap_normalizedFlattening_reducedProjection` gives the
  compressed trace formula for the reduced projection.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188,
  equation `eq:transfer-op`, lines 336--340, and Proposition IV.5,
  lines 747--783.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Virtual sandwiching transforms the normalized transfer map by sandwiching
its input and output. No invertibility or positivity assumptions are needed.

Source: arXiv:1703.09188, equation `eq:transfer-op`, lines 336--340,
and Proposition IV.5, lines 778--781. -/
theorem transferMap_normalizedFlattening_virtualSandwich
    (A B : Matrix (Fin D) (Fin D) ℂ) (W : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.transferMap (virtualSandwich A W B).normalizedFlattening X =
      A * Kraus.transferMap W.normalizedFlattening (B * X * Bᴴ) * Aᴴ := by
  have h : (virtualSandwich A W B).normalizedFlattening =
      fun ij ↦ A * W.normalizedFlattening ij * B := by
    funext ij
    simp only [normalizedFlattening, toMPSTensor,
      virtualSandwich_apply, Matrix.mul_smul, Matrix.smul_mul]
  simp only [h, Kraus.transferMap_apply, Matrix.conjTranspose_mul,
    Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]

/-- The normalized transfer map of the reduced tensor has the compressed
trace formula. The same normalization is used in both the hypothesis and
the conclusion, and the fixed pair is supplied explicitly.

Source: arXiv:1703.09188, Proposition IV.5, lines 747--752 and 778--781. -/
theorem transferMap_normalizedFlattening_reducedProjection
    (W : MPOTensor d D) (L R P Q : Matrix (Fin D) (Fin D) ℂ)
    (hTransfer : ∀ X, Kraus.transferMap W.normalizedFlattening X =
      Matrix.trace (L * X) • R) (X : Matrix (Fin D) (Fin D) ℂ) :
    let T := Matrix.reducedProjection P Q
    Kraus.transferMap (virtualSandwich T W T).normalizedFlattening X =
      Matrix.trace ((T * L * T) * X) • (T * R * T) := by
  let T := Matrix.reducedProjection P Q
  have hT := (Matrix.reducedProjection_isOrthogonalProjection P Q).1
  dsimp only
  rw [transferMap_normalizedFlattening_virtualSandwich, hT.eq, hTransfer,
    Matrix.mul_smul, Matrix.smul_mul]
  exact congrArg (fun c : ℂ ↦ c • (T * R * T)) (by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (L * (T * X)) T)

end MPOTensor
