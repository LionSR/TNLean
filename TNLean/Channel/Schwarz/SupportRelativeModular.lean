/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.ResolventFunctionalCalculus
import TNLean.Channel.PetzRecovery

/-!
# Relative modular square roots on singular supports

This file proves the support-domain passage from equality of relative-modular
resolvents to equality of square-root ratios. The generalized inverse of the
reference matrix is represented as the square of its support inverse square root.

## Main results

* `Matrix.supportRelativeModular_sqrt_mulVec_vec_one` evaluates the positive
  square root of the support relative-modular matrix on the vectorized identity.
* `Matrix.supportRelativeModular_sqrt_ratio_eq_of_resolvent_mulVec_eq` turns a
  common family of shifted resolvents into equality of support square-root ratios.

## References

* A. Jenčová and M. B. Ruskai, *A Unified Treatment of Convexity of Relative
  Entropy and Related Trace Functions, with Conditions for Equality*,
  arXiv:0903.2895v4, §4.2, lines 717--720 and 766--793.
-/

open scoped Matrix ComplexOrder Kronecker MatrixOrder

namespace Matrix

/-- The positive square root of the support relative-modular matrix, applied to
the vectorized identity, is the vectorization of the support square-root ratio.

The generalized inverse convention is that of Jenčová--Ruskai,
arXiv:0903.2895v4, lines 255--261. The singular equality argument uses this
convention on the reference support in §4.2, lines 766--793. -/
theorem supportRelativeModular_sqrt_mulVec_vec_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (A ⊗ₖ
        (hB.supportInvSqrt * hB.supportInvSqrt)ᵀ) *ᵥ
        Matrix.vec (1 : Matrix n n ℂ)ᵀ =
      Matrix.vec (CFC.sqrt A * hB.supportInvSqrt)ᵀ := by
  let qA : Matrix n n ℂ := CFC.sqrt A
  let qBInv : Matrix n n ℂ := hB.supportInvSqrt
  let delta : Matrix (n × n) (n × n) ℂ := A ⊗ₖ (qBInv * qBInv)ᵀ
  let qDelta : Matrix (n × n) (n × n) ℂ := qA ⊗ₖ qBInvᵀ
  have hqA : qA.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hqBInv : qBInv.PosSemidef := hB.supportInvSqrt_posSemidef
  have hqBInv_sq : (qBInv * qBInv).PosSemidef := by
    simpa [hqBInv.isHermitian.eq] using posSemidef_conjTranspose_mul_self qBInv
  have hdelta : delta.PosSemidef := hA.kronecker hqBInv_sq.transpose
  have hqDelta : qDelta.PosSemidef := hqA.kronecker hqBInv.transpose
  have hqA_sq : qA * qA = A := by
    simpa only [qA] using CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hqDelta_sq : qDelta * qDelta = delta := by
    dsimp only [qDelta, delta]
    rw [← Matrix.mul_kronecker_mul, hqA_sq, ← Matrix.transpose_mul]
  have hsqrt : CFC.sqrt delta = qDelta := by
    apply (CFC.sqrt_eq_iff delta qDelta hdelta.nonneg hqDelta.nonneg).2
    exact hqDelta_sq
  change CFC.sqrt delta *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ =
    Matrix.vec (qA * qBInv)ᵀ
  rw [hsqrt]
  dsimp only [qDelta]
  rw [Matrix.kronecker_mulVec_vec]
  simp only [Matrix.transpose_one, Matrix.mul_one, Matrix.transpose_mul]

/-- Equality of all positive shifted support relative-modular resolvents on the
vectorized identity implies equality of the corresponding support square-root
ratios.

This is the positive-square-root specialization of the singular-support
functional-calculus step in Jenčová--Ruskai, arXiv:0903.2895v4, §4.2,
lines 766--793. Their preceding equality argument is stated for supported pairs,
but the functional-calculus implication here needs only positive semidefiniteness
and the common resolvents. This theorem does not assert that equality for
regularized pairs follows from equality of the original pair. -/
theorem supportRelativeModular_sqrt_ratio_eq_of_resolvent_mulVec_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B C D : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hC : C.PosSemidef) (hD : D.PosSemidef)
    (hres : ∀ {t : ℝ}, 0 < t →
      (t • (1 : Matrix (n × n) (n × n) ℂ) +
          A ⊗ₖ (hB.supportInvSqrt * hB.supportInvSqrt)ᵀ)⁻¹ *ᵥ
          Matrix.vec (1 : Matrix n n ℂ)ᵀ =
        (t • (1 : Matrix (n × n) (n × n) ℂ) +
          C ⊗ₖ (hD.supportInvSqrt * hD.supportInvSqrt)ᵀ)⁻¹ *ᵥ
          Matrix.vec (1 : Matrix n n ℂ)ᵀ) :
    CFC.sqrt A * hB.supportInvSqrt =
      CFC.sqrt C * hD.supportInvSqrt := by
  have hBInvSq : (hB.supportInvSqrt * hB.supportInvSqrt).PosSemidef := by
    simpa [hB.supportInvSqrt_isHermitian.eq] using
      posSemidef_conjTranspose_mul_self hB.supportInvSqrt
  have hDInvSq : (hD.supportInvSqrt * hD.supportInvSqrt).PosSemidef := by
    simpa [hD.supportInvSqrt_isHermitian.eq] using
      posSemidef_conjTranspose_mul_self hD.supportInvSqrt
  have hsqrt := sqrt_mulVec_eq_of_resolvent_mulVec_eq
    (hA.kronecker hBInvSq.transpose)
    (hC.kronecker hDInvSq.transpose) hres
  rw [supportRelativeModular_sqrt_mulVec_vec_one hA hB,
    supportRelativeModular_sqrt_mulVec_vec_one hC hD] at hsqrt
  exact Matrix.transpose_injective (Matrix.vec_inj.mp hsqrt)

end Matrix
