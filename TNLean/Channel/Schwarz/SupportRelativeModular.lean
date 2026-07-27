/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.RelativeEntropySupportLeftRightQuadratic
import TNLean.Analysis.ResolventFunctionalCalculus

/-!
# Relative modular square roots on singular supports

This file proves the support-domain passage from equality of relative-modular
resolvents to equality of square-root ratios. The generalized inverse of the
reference matrix is represented as the square of its support inverse square root.

## Main results

* `Matrix.one_kronecker_transpose_mulVec_vec_transpose` identifies the
  Kronecker matrix that represents right multiplication on a transposed
  vectorization.
* `Matrix.supportRelativeModular_resolvent_posDef` and
  `Matrix.supportLeftRightSuperoperator_mul_supportProj_eq` give positivity and
  the support-resolvent intertwining identity.
* `Matrix.supportRelativeModular_sqrt_mulVec_vec_one` evaluates the positive
  square root of the support relative-modular matrix on the vectorized identity.
* `Matrix.supportRelativeModular_sourceB_solution` gives the canonical
  support-domain solution of the singular source resolvent equation.
* `Matrix.supportRelativeModular_sqrt_ratio_eq_of_resolvent_mulVec_eq` turns a
  support-restricted common family of shifted resolvents into equality of
  support-restricted square-root ratios.

## References

* A. Jenčová and M. B. Ruskai, *A Unified Treatment of Convexity of Relative
  Entropy and Related Trace Functions, with Conditions for Equality*,
  arXiv:0903.2895v4, §4.2, lines 766--793.

The preceding singular equality-to-resolvent step is formalized downstream in
`TNLean.Channel.Schwarz.SupportRelativeEntropyEquality`. The later
support functional-calculus and recovery steps are tracked in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`.
-/

open scoped Matrix ComplexOrder Kronecker MatrixOrder

namespace Matrix

/-- Under column-stacking vectorization, `1 ⊗ Pᵀ` represents right
multiplication by `P` when the matrix itself is transposed before
vectorization. -/
theorem one_kronecker_transpose_mulVec_vec_transpose
    {n : Type*} [Fintype n] [DecidableEq n]
    (M P : Matrix n n ℂ) :
    ((1 : Matrix n n ℂ) ⊗ₖ Pᵀ) *ᵥ Matrix.vec Mᵀ =
      Matrix.vec (M * P)ᵀ := by
  rw [Matrix.kronecker_mulVec_vec]
  simp only [Matrix.transpose_mul, Matrix.transpose_one, Matrix.mul_one]

/-- A positive shift of the support relative-modular matrix is positive definite. -/
theorem supportRelativeModular_resolvent_posDef
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    (t • (1 : Matrix (n × n) (n × n) ℂ) +
      A ⊗ₖ hB.supportInvᵀ).PosDef := by
  have hBplusPSD : hB.supportInv.PosSemidef := by
    simpa only [PosSemidef.supportInv, hB.supportInvSqrt_isHermitian.eq] using
      posSemidef_conjTranspose_mul_self hB.supportInvSqrt
  exact (Matrix.PosDef.one.smul ht).add_posSemidef
    (hA.kronecker hBplusPSD.transpose)

/-- The support projection intertwines the left-right operator with the shifted
support relative-modular matrix. -/
theorem supportLeftRightSuperoperator_mul_supportProj_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hB : B.PosSemidef) (t : ℝ) :
    supportLeftRightSuperoperator A B t *
        ((1 : Matrix n n ℂ) ⊗ₖ hB.isHermitian.supportProjᵀ) =
      ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ) *
        (t • (1 : Matrix (n × n) (n × n) ℂ) +
          A ⊗ₖ hB.supportInvᵀ) := by
  have hCdelta :
      ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ) * (A ⊗ₖ hB.supportInvᵀ) =
        A ⊗ₖ hB.isHermitian.supportProjᵀ := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      ← Matrix.transpose_mul, hB.supportInv_mul_self]
  have hBTP : Bᵀ * hB.isHermitian.supportProjᵀ = Bᵀ := by
    rw [← Matrix.transpose_mul, hB.isHermitian.supportProj_mul_self]
  rw [supportLeftRightSuperoperator, Matrix.add_mul, Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, hBTP, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_one, hCdelta]
  simp only [Matrix.mul_one]
  abel

/-- The canonical support-domain vector built from the generalized relative
modular resolvent solves the singular source equation.

This is the algebraic source-side resolvent identity used in the equality
argument of Jenčová--Ruskai, arXiv:0903.2895v4, lines 783--790, with the
generalized inverse convention from lines 255--261. It does not derive a
common resolvent from equality in data processing. -/
theorem supportRelativeModular_sourceB_solution
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    let Bplus := hB.supportInvSqrt * hB.supportInvSqrt
    let delta := A ⊗ₖ Bplusᵀ
    let res := t • (1 : Matrix (n × n) (n × n) ℂ) + delta
    let P := (1 : Matrix n n ℂ) ⊗ₖ hB.isHermitian.supportProjᵀ
    let S := A ⊗ₖ (1 : Matrix n n ℂ) +
      t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)
    S *ᵥ (P *ᵥ (res⁻¹ *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ)) =
      Matrix.vec Bᵀ := by
  dsimp only
  let Bplus := hB.supportInvSqrt * hB.supportInvSqrt
  let delta := A ⊗ₖ Bplusᵀ
  let res := t • (1 : Matrix (n × n) (n × n) ℂ) + delta
  let P := (1 : Matrix n n ℂ) ⊗ₖ hB.isHermitian.supportProjᵀ
  let S := A ⊗ₖ (1 : Matrix n n ℂ) +
    t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)
  let C := (1 : Matrix n n ℂ) ⊗ₖ Bᵀ
  have hres : res.PosDef := by
    simpa only [res, delta, Bplus, PosSemidef.supportInv] using
      supportRelativeModular_resolvent_posDef hA hB ht
  letI : Invertible res := hres.isUnit.invertible
  have hSP : S * P = C * res := by
    simpa only [S, supportLeftRightSuperoperator, P, C, res, delta, Bplus,
      PosSemidef.supportInv] using
        supportLeftRightSuperoperator_mul_supportProj_eq (A := A) hB t
  have hCe : C *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ = Matrix.vec Bᵀ := by
    simpa only [C, Matrix.one_mul] using
      one_kronecker_transpose_mulVec_vec_transpose (1 : Matrix n n ℂ) B
  calc
    S *ᵥ (P *ᵥ (res⁻¹ *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ)) =
        (S * P) *ᵥ (res⁻¹ *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ) :=
      Matrix.mulVec_mulVec
        (res⁻¹ *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ) S P
    _ = (C * res) *ᵥ (res⁻¹ *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ) := by
      rw [hSP]
    _ = C *ᵥ ((res * res⁻¹) *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = C *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ := by
      rw [Matrix.mul_inv_of_invertible]
      simp
    _ = Matrix.vec Bᵀ := hCe

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

/-- Equality of all positive shifted relative-modular resolvents on the
vectorized identity, after restriction to the support of the first reference
matrix, implies equality of the square-root ratios on that support.

This is the positive-square-root specialization of the singular-support
functional-calculus step in Jenčová--Ruskai, arXiv:0903.2895v4, §4.2,
lines 788--793. The restriction by the support projection is essential: the
source asserts equality only on the complement of the kernel of the smaller
reference matrix. The required finite-family resolvent equality from
relative-entropy equality is supplied downstream by
`supportRelativeModular_resolvent_mulVec_eq_of_relativeEntropy_sum_eq`. -/
theorem supportRelativeModular_sqrt_ratio_eq_of_resolvent_mulVec_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B C D : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hC : C.PosSemidef) (hD : D.PosSemidef)
    (hres : ∀ {t : ℝ}, 0 < t →
      ((1 : Matrix n n ℂ) ⊗ₖ hB.isHermitian.supportProjᵀ) *ᵥ
          ((t • (1 : Matrix (n × n) (n × n) ℂ) +
            A ⊗ₖ (hB.supportInvSqrt * hB.supportInvSqrt)ᵀ)⁻¹ *ᵥ
            Matrix.vec (1 : Matrix n n ℂ)ᵀ) =
        ((1 : Matrix n n ℂ) ⊗ₖ hB.isHermitian.supportProjᵀ) *ᵥ
          ((t • (1 : Matrix (n × n) (n × n) ℂ) +
            C ⊗ₖ (hD.supportInvSqrt * hD.supportInvSqrt)ᵀ)⁻¹ *ᵥ
            Matrix.vec (1 : Matrix n n ℂ)ᵀ)) :
    (CFC.sqrt A * hB.supportInvSqrt) * hB.isHermitian.supportProj =
      (CFC.sqrt C * hD.supportInvSqrt) * hB.isHermitian.supportProj := by
  have hBInvSq : (hB.supportInvSqrt * hB.supportInvSqrt).PosSemidef := by
    simpa [hB.supportInvSqrt_isHermitian.eq] using
      posSemidef_conjTranspose_mul_self hB.supportInvSqrt
  have hDInvSq : (hD.supportInvSqrt * hD.supportInvSqrt).PosSemidef := by
    simpa [hD.supportInvSqrt_isHermitian.eq] using
      posSemidef_conjTranspose_mul_self hD.supportInvSqrt
  have hsqrt := mulVec_sqrt_mulVec_eq_of_mulVec_resolvent_mulVec_eq
    (hA.kronecker hBInvSq.transpose)
    (hC.kronecker hDInvSq.transpose) hres
  rw [supportRelativeModular_sqrt_mulVec_vec_one hA hB,
    supportRelativeModular_sqrt_mulVec_vec_one hC hD] at hsqrt
  rw [one_kronecker_transpose_mulVec_vec_transpose,
    one_kronecker_transpose_mulVec_vec_transpose] at hsqrt
  exact Matrix.transpose_injective (Matrix.vec_inj.mp hsqrt)

end Matrix
