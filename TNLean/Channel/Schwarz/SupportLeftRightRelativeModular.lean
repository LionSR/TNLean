/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.RelativeEntropySupportLeftRightQuadratic
import TNLean.Channel.Schwarz.SupportRelativeModular

/-!
# Support left-right and relative-modular resolvents

For positive-semidefinite matrices \(A\) and \(B\), let
\[
  S=A\otimes 1+t(1\otimes B^{\mathsf T}),\qquad
  P=1\otimes P_B^{\mathsf T},
\]
and let
\[
  R=t1+A\otimes(B^+)^{\mathsf T},
\]
where \(P_B\) is the support projection of \(B\) and \(B^+\) is its generalized
inverse on the support. This file proves that the support-generalized-inverse
solution \(S^+\operatorname{vec}(B^{\mathsf T})\) is the canonical projected
relative-modular solution
\[
  P R^{-1}\operatorname{vec}(1^{\mathsf T}).
\]

## Main results

* `Matrix.supportLeftRightSupportInv_mulVec_sourceB_eq_projected_relativeModular`
  identifies the two source-\(B\) solution vectors.
* `Matrix.supportSourceBQuadratic_eq_projected_relativeModular` gives the
  corresponding equality of quadratic forms.

## References

* A. Jenčová and M. B. Ruskai, *A Unified Treatment of Convexity of Relative
  Entropy and Related Trace Functions, with Conditions for Equality*,
  arXiv:0903.2895v4, lines 255--261 and 783--790.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker

namespace Matrix

/-- The support-generalized-inverse source-\(B\) solution of the left-right
operator is the projected shifted relative-modular solution:
\[
  S^+\operatorname{vec}(B^{\mathsf T})
  =
  (1\otimes P_B^{\mathsf T})
  \bigl(t1+A\otimes(B^+)^{\mathsf T}\bigr)^{-1}
  \operatorname{vec}(1^{\mathsf T}).
\]

This is the one-pair algebraic identity used in the singular equality argument
of Jenčová--Ruskai, arXiv:0903.2895v4, lines 783--790, with the generalized
inverse convention from lines 255--261. It does not derive a common resolvent
from equality of relative entropies. -/
theorem supportLeftRightSupportInv_mulVec_sourceB_eq_projected_relativeModular
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    supportLeftRightSupportInv hA hB t *ᵥ Matrix.vec Bᵀ =
      ((1 : Matrix n n ℂ) ⊗ₖ hB.isHermitian.supportProjᵀ) *ᵥ
        ((t • (1 : Matrix (n × n) (n × n) ℂ) +
          A ⊗ₖ hB.supportInvᵀ)⁻¹ *ᵥ
            Matrix.vec (1 : Matrix n n ℂ)ᵀ) := by
  let Bplus := hB.supportInv
  let delta := A ⊗ₖ Bplusᵀ
  let res := t • (1 : Matrix (n × n) (n × n) ℂ) + delta
  let P := (1 : Matrix n n ℂ) ⊗ₖ hB.isHermitian.supportProjᵀ
  let S := supportLeftRightSuperoperator A B t
  let C := (1 : Matrix n n ℂ) ⊗ₖ Bᵀ
  let D := (1 : Matrix n n ℂ) ⊗ₖ Bplusᵀ
  let e : n × n → ℂ := Matrix.vec (1 : Matrix n n ℂ)ᵀ
  let b : n × n → ℂ := Matrix.vec Bᵀ
  let y : n × n → ℂ := P *ᵥ (res⁻¹ *ᵥ e)
  have hBplus_mul : Bplus * B = hB.isHermitian.supportProj := by
    simpa only [Bplus] using hB.supportInv_mul_self
  have hBplusPSD : Bplus.PosSemidef := by
    simpa only [Bplus, PosSemidef.supportInv,
      hB.supportInvSqrt_isHermitian.eq] using
        posSemidef_conjTranspose_mul_self hB.supportInvSqrt
  have hdelta : delta.PosSemidef := hA.kronecker hBplusPSD.transpose
  have hres : res.PosDef :=
    (Matrix.PosDef.one.smul ht).add_posSemidef hdelta
  letI : Invertible res := hres.isUnit.invertible
  have hCdelta :
      C * delta = A ⊗ₖ hB.isHermitian.supportProjᵀ := by
    dsimp only [C, delta]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      ← Matrix.transpose_mul, hBplus_mul]
  have hBTP : Bᵀ * hB.isHermitian.supportProjᵀ = Bᵀ := by
    rw [← Matrix.transpose_mul, hB.isHermitian.supportProj_mul_self]
  have hSP : S * P = C * res := by
    dsimp only [S, supportLeftRightSuperoperator, P, C, res]
    rw [Matrix.add_mul, Matrix.smul_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul, hBTP,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hCdelta]
    simp only [Matrix.mul_one]
    abel
  have hCD : C * D = P := by
    dsimp only [C, D, P]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      ← Matrix.transpose_mul, hBplus_mul]
  have hPidem : P * P = P := by
    dsimp only [P]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      ← Matrix.transpose_mul, hB.isHermitian.supportProj_idem]
  have hyP : P *ᵥ y = y := by
    calc
      P *ᵥ y = (P * P) *ᵥ (res⁻¹ *ᵥ e) := by
        exact Matrix.mulVec_mulVec (res⁻¹ *ᵥ e) P P
      _ = y := by rw [hPidem]
  have hsolution : S *ᵥ y = b := by
    simpa only [Bplus, PosSemidef.supportInv, delta, res, P, S,
      supportLeftRightSuperoperator, e, b, y] using
        supportRelativeModular_sourceB_solution hA hB ht
  let w : n × n → ℂ := P *ᵥ (res⁻¹ *ᵥ (D *ᵥ y))
  have hrange : S *ᵥ w = y := by
    calc
      S *ᵥ w = (S * P) *ᵥ (res⁻¹ *ᵥ (D *ᵥ y)) := by
        exact Matrix.mulVec_mulVec (res⁻¹ *ᵥ (D *ᵥ y)) S P
      _ = (C * res) *ᵥ (res⁻¹ *ᵥ (D *ᵥ y)) := by rw [hSP]
      _ = C *ᵥ ((res * res⁻¹) *ᵥ (D *ᵥ y)) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = C *ᵥ (D *ᵥ y) := by
        rw [Matrix.mul_inv_of_invertible]
        simp
      _ = (C * D) *ᵥ y := Matrix.mulVec_mulVec y C D
      _ = P *ᵥ y := by rw [hCD]
      _ = y := hyP
  have hS : S.PosSemidef := by
    simpa only [S] using
      supportLeftRightSuperoperator_posSemidef hA hB ht.le
  have hySupport : hS.isHermitian.supportProj *ᵥ y = y := by
    rw [← hrange]
    conv_lhs => rw [Matrix.mulVec_mulVec]
    rw [hS.isHermitian.supportProj_mul_self]
  have hsupportInv : hS.supportInv *ᵥ b = y := by
    calc
      hS.supportInv *ᵥ b =
          hS.supportInv *ᵥ (S *ᵥ y) := by rw [hsolution]
      _ = (hS.supportInv * S) *ᵥ y := Matrix.mulVec_mulVec y hS.supportInv S
      _ = y := by rw [hS.supportInv_mul_self, hySupport]
  rw [supportLeftRightSupportInv_eq hA hB ht.le]
  change
    (supportLeftRightSuperoperator_posSemidef hA hB ht.le).supportInv *ᵥ b = y
  rw [show
    (supportLeftRightSuperoperator_posSemidef hA hB ht.le).supportInv =
      hS.supportInv from rfl]
  exact hsupportInv

/-- The source-\(B\) quadratic form of the support left-right operator equals
its evaluation on the projected shifted relative-modular solution.

This is the quadratic-form consequence of the one-pair identity used in
Jenčová--Ruskai, arXiv:0903.2895v4, lines 783--790. It contains no implication
from equality of relative entropies. -/
theorem supportSourceBQuadratic_eq_projected_relativeModular
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    supportSourceBQuadratic hA hB t =
      (star (Matrix.vec Bᵀ) ⬝ᵥ
        (((1 : Matrix n n ℂ) ⊗ₖ hB.isHermitian.supportProjᵀ) *ᵥ
          ((t • (1 : Matrix (n × n) (n × n) ℂ) +
            A ⊗ₖ hB.supportInvᵀ)⁻¹ *ᵥ
              Matrix.vec (1 : Matrix n n ℂ)ᵀ))).re := by
  unfold supportSourceBQuadratic
  rw [supportLeftRightSupportInv_mulVec_sourceB_eq_projected_relativeModular
    hA hB ht]

end Matrix
