/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import TNLean.Analysis.MatrixSqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Residual identities on matrix supports

This file proves the residual identity for a finite family of positive-semidefinite
matrices and source vectors in their supports. The inverse is the generalized inverse
defined by the inverse square root on the support. Vanishing of the resulting defect
gives a common generalized-inverse solution after projection to each support.

## Main results

* `Matrix.support_resolvent_residual_identity`: the difference of the
  generalized-inverse quadratic forms is a sum of residual quadratic forms.
* `Matrix.support_resolvent_eq_of_defect_eq_zero`: zero defect gives a common
  solution after projection to each support.

## References

* A. Jenčová and M. B. Ruskai, arXiv:0903.2895v4, Appendix, equations `(Mj)`
  and `(eq:Schz1)`, and §3.1, equation `(basiceq)`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n]

variable [DecidableEq n]

private lemma support_resolvent_residual_expand
    (S : Matrix n n ℂ) (hS : S.PosSemidef) (b x : n → ℂ)
    (hb : hS.isHermitian.supportProj *ᵥ b = b) :
    let G := hS.supportInvSqrt * hS.supportInvSqrt
    dotProduct (star (b - S *ᵥ x)) (G *ᵥ (b - S *ᵥ x)) =
      dotProduct (star b) (G *ᵥ b) - dotProduct (star b) x -
        dotProduct (star x) b + dotProduct (star x) (S *ᵥ x) := by
  dsimp only
  let G := hS.supportInvSqrt * hS.supportInvSqrt
  let P := hS.isHermitian.supportProj
  have hGS : G * S = P := by
    simpa only [G, P] using hS.supportInvSqrt_sq_mul_self
  have hSG : S * G = P := by
    simpa only [G, P] using hS.self_mul_supportInvSqrt_sq
  have hPb (y : n → ℂ) :
      dotProduct (star b) (P *ᵥ y) = dotProduct (star b) y := by
    rw [← hS.isHermitian.supportProj_isHermitian.star_mulVec_dotProduct b y]
    rw [hb]
  simp only [star_sub, sub_dotProduct, mulVec_sub, dotProduct_sub]
  rw [mulVec_mulVec, hGS, hPb]
  rw [hS.isHermitian.star_mulVec_dotProduct]
  rw [mulVec_mulVec, hSG, hb]
  rw [hS.isHermitian.star_mulVec_dotProduct]
  rw [mulVec_mulVec]
  rw [show S * P = S from hS.isHermitian.mul_supportProj_self]
  ring

/-- **The support-resolvent residual identity.** For a finite family of
positive-semidefinite matrices, suppose that every source vector lies in the
support of its matrix, and that the summed source vector lies in the support
of the summed matrix. The difference of the generalized-inverse quadratic
forms is then the sum of the generalized-inverse quadratic residuals.

The residual expansion is the support-domain counterpart of
Jenčová--Ruskai, arXiv:0903.2895v4, Appendix, equations `(Mj)` and
`(eq:Schz1)`. The source states that calculation for positive-definite
matrices; the support hypotheses here make the same calculation exact for
generalized inverses of positive-semidefinite matrices. -/
theorem support_resolvent_residual_identity
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : ι → Matrix n n ℂ) (b : ι → n → ℂ)
    (hS : ∀ i, (S i).PosSemidef)
    (hb : ∀ i, (hS i).isHermitian.supportProj *ᵥ b i = b i)
    (hbar :
      let Sbar := ∑ i, S i
      let bbar := ∑ i, b i
      let hSbar : Sbar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
      hSbar.isHermitian.supportProj *ᵥ bbar = bbar) :
    let Sbar := ∑ i, S i
    let bbar := ∑ i, b i
    let G := fun i ↦ (hS i).supportInvSqrt * (hS i).supportInvSqrt
    let hSbar : Sbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
    let Gbar := hSbar.supportInvSqrt * hSbar.supportInvSqrt
    let x := Gbar *ᵥ bbar
    ∑ i, dotProduct (star (b i - S i *ᵥ x))
      (G i *ᵥ (b i - S i *ᵥ x)) =
      (∑ i, dotProduct (star (b i)) (G i *ᵥ b i)) -
        dotProduct (star bbar) (Gbar *ᵥ bbar) := by
  classical
  dsimp only
  let Sbar : Matrix n n ℂ := ∑ i, S i
  let bbar : n → ℂ := ∑ i, b i
  let hSbar : Sbar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
  let G : ι → Matrix n n ℂ := fun i ↦
    (hS i).supportInvSqrt * (hS i).supportInvSqrt
  let Gbar : Matrix n n ℂ := hSbar.supportInvSqrt * hSbar.supportInvSqrt
  let x : n → ℂ := Gbar *ᵥ bbar
  have hx : Sbar *ᵥ x = bbar := by
    dsimp only [x]
    rw [mulVec_mulVec]
    rw [show Sbar * Gbar = hSbar.isHermitian.supportProj from by
      simpa only [Gbar] using hSbar.self_mul_supportInvSqrt_sq]
    exact hbar
  have hsumStarB : ∑ i, star (b i) = star bbar := by
    ext j
    simp [bbar]
  have hsumB : ∑ i, b i = bbar := rfl
  have hsumSx : ∑ i, S i *ᵥ x = Sbar *ᵥ x := by
    simpa [Sbar] using (Matrix.sum_mulVec Finset.univ S x).symm
  change (∑ i, dotProduct (star (b i - S i *ᵥ x))
      (G i *ᵥ (b i - S i *ᵥ x))) =
    (∑ i, dotProduct (star (b i)) (G i *ᵥ b i)) -
      dotProduct (star bbar) (Gbar *ᵥ bbar)
  simp_rw [show ∀ i, dotProduct (star (b i - S i *ᵥ x))
      (G i *ᵥ (b i - S i *ᵥ x)) =
        dotProduct (star (b i)) (G i *ᵥ b i) - dotProduct (star (b i)) x -
          dotProduct (star x) (b i) + dotProduct (star x) (S i *ᵥ x) from
    fun i ↦ by
      simpa only [G] using support_resolvent_residual_expand (S i) (hS i)
        (b i) x (hb i)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hleft : ∑ i, dotProduct (star (b i)) x = dotProduct (star bbar) x := by
    rw [← hsumStarB]
    simpa using (sum_dotProduct Finset.univ (fun i ↦ star (b i)) x).symm
  have hright : ∑ i, dotProduct (star x) (b i) = dotProduct (star x) bbar := by
    rw [← hsumB]
    simpa using (dotProduct_sum (star x) Finset.univ b).symm
  have hlast : ∑ i, dotProduct (star x) (S i *ᵥ x) =
      dotProduct (star x) (Sbar *ᵥ x) := by
    rw [← hsumSx]
    simpa using (dotProduct_sum (star x) Finset.univ (fun i ↦ S i *ᵥ x)).symm
  rw [hleft, hright, hlast, hx]
  ring

/-- **The finite-family support-resolvent quadratic defect is nonnegative.**
Under the hypotheses of `support_resolvent_residual_identity`, the sum of the
support-generalized-inverse quadratic forms dominates the quadratic form of
the summed matrix and source:
\[
  0 \leq \operatorname{Re}\left(
    \sum_i \langle b_i,S_i^+b_i\rangle
      -\left\langle\sum_i b_i,
        \left(\sum_i S_i\right)^+\sum_i b_i\right\rangle\right).
\]

This is the support-domain consequence of the residual calculation in
Jenčová--Ruskai, arXiv:0903.2895v4, Appendix, equations `(Mj)`,
`(eq:Schz1)`, and `(eq:Schwzt)`. -/
lemma support_resolvent_quadratic_sum_sub_nonneg
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : ι → Matrix n n ℂ) (b : ι → n → ℂ)
    (hS : ∀ i, (S i).PosSemidef)
    (hb : ∀ i, (hS i).isHermitian.supportProj *ᵥ b i = b i)
    (hbar :
      let Sbar := ∑ i, S i
      let bbar := ∑ i, b i
      let hSbar : Sbar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
      hSbar.isHermitian.supportProj *ᵥ bbar = bbar) :
    let Sbar := ∑ i, S i
    let bbar := ∑ i, b i
    let G := fun i ↦ (hS i).supportInv
    let hSbar : Sbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
    let Gbar := hSbar.supportInv
    0 ≤ ((∑ i, dotProduct (star (b i)) (G i *ᵥ b i)) -
      dotProduct (star bbar) (Gbar *ᵥ bbar)).re := by
  classical
  dsimp only
  let Sbar : Matrix n n ℂ := ∑ i, S i
  let bbar : n → ℂ := ∑ i, b i
  let hSbar : Sbar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
  let G : ι → Matrix n n ℂ := fun i ↦ (hS i).supportInv
  let Gbar : Matrix n n ℂ := hSbar.supportInv
  let x : n → ℂ := Gbar *ᵥ bbar
  have hres :
      ∑ i, dotProduct (star (b i - S i *ᵥ x))
        (G i *ᵥ (b i - S i *ᵥ x)) =
        (∑ i, dotProduct (star (b i)) (G i *ᵥ b i)) -
          dotProduct (star bbar) (Gbar *ᵥ bbar) := by
    simpa only [Sbar, bbar, hSbar, G, Gbar, x,
      Matrix.PosSemidef.supportInv] using
      support_resolvent_residual_identity S b hS hb hbar
  have hresidual_nonneg :
      (0 : ℂ) ≤ ∑ i, dotProduct (star (b i - S i *ᵥ x))
        (G i *ᵥ (b i - S i *ᵥ x)) := by
    apply Finset.sum_nonneg
    intro i _
    have hGi : (G i).PosSemidef := by
      simpa only [G, Matrix.PosSemidef.supportInv,
        (hS i).supportInvSqrt_isHermitian.eq] using
        posSemidef_conjTranspose_mul_self (hS i).supportInvSqrt
    exact hGi.dotProduct_mulVec_nonneg (b i - S i *ᵥ x)
  rw [hres] at hresidual_nonneg
  exact (Complex.nonneg_iff.mp hresidual_nonneg).1

/-- **Zero support-resolvent defect gives a common solution on each
support.** Under the hypotheses of `support_resolvent_residual_identity`, if
the generalized-inverse quadratic defect vanishes, then the generalized
solution for each summand is the restriction of the summed solution to that
summand's support.

This is the support-domain form of the common-resolvent conclusion
`(basiceq)` in Jenčová--Ruskai, arXiv:0903.2895v4, §3.1. Its residual
calculation is the one in the Appendix, equations `(Mj)` and `(eq:Schz1)`. -/
theorem support_resolvent_eq_of_defect_eq_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : ι → Matrix n n ℂ) (b : ι → n → ℂ)
    (hS : ∀ i, (S i).PosSemidef)
    (hb : ∀ i, (hS i).isHermitian.supportProj *ᵥ b i = b i)
    (hbar :
      let Sbar := ∑ i, S i
      let bbar := ∑ i, b i
      let hSbar : Sbar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
      hSbar.isHermitian.supportProj *ᵥ bbar = bbar)
    (hzero :
      let Sbar := ∑ i, S i
      let bbar := ∑ i, b i
      let G := fun i ↦ (hS i).supportInvSqrt * (hS i).supportInvSqrt
      let hSbar : Sbar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
      let Gbar := hSbar.supportInvSqrt * hSbar.supportInvSqrt
      (∑ i, dotProduct (star (b i)) (G i *ᵥ b i)) -
        dotProduct (star bbar) (Gbar *ᵥ bbar) = 0) :
    let Sbar := ∑ i, S i
    let bbar := ∑ i, b i
    let G := fun i ↦ (hS i).supportInvSqrt * (hS i).supportInvSqrt
    let hSbar : Sbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
    let Gbar := hSbar.supportInvSqrt * hSbar.supportInvSqrt
    let x := Gbar *ᵥ bbar
    ∀ i, G i *ᵥ b i = (hS i).isHermitian.supportProj *ᵥ x := by
  classical
  dsimp only
  let Sbar : Matrix n n ℂ := ∑ i, S i
  let bbar : n → ℂ := ∑ i, b i
  let hSbar : Sbar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
  let G : ι → Matrix n n ℂ := fun i ↦
    (hS i).supportInvSqrt * (hS i).supportInvSqrt
  let Gbar : Matrix n n ℂ := hSbar.supportInvSqrt * hSbar.supportInvSqrt
  let x : n → ℂ := Gbar *ᵥ bbar
  have hresid := support_resolvent_residual_identity S b hS hb hbar
  have hreszero :
      ∑ i, dotProduct (star (b i - S i *ᵥ x))
        (G i *ᵥ (b i - S i *ᵥ x)) = 0 := by
    rw [hresid]
    exact hzero
  intro i
  let H : Matrix n n ℂ := (hS i).supportInvSqrt
  let P : Matrix n n ℂ := (hS i).isHermitian.supportProj
  have hG : (G i).PosSemidef := by
    simpa only [G, H, (hS i).supportInvSqrt_isHermitian.eq] using
      posSemidef_conjTranspose_mul_self H
  have hnonneg : ∀ j, 0 ≤ dotProduct (star (b j - S j *ᵥ x))
      (G j *ᵥ (b j - S j *ᵥ x)) := by
    intro j
    have hGj : (G j).PosSemidef := by
      simpa only [G, (hS j).supportInvSqrt_isHermitian.eq] using
        posSemidef_conjTranspose_mul_self (hS j).supportInvSqrt
    exact hGj.dotProduct_mulVec_nonneg (b j - S j *ᵥ x)
  have hterm : dotProduct (star (b i - S i *ᵥ x))
      (G i *ᵥ (b i - S i *ᵥ x)) = 0 := by
    exact congrFun (Fintype.sum_eq_zero_iff_of_nonneg hnonneg |>.mp hreszero) i
  have hGr : G i *ᵥ (b i - S i *ᵥ x) = 0 :=
    (hG.dotProduct_mulVec_zero_iff (b i - S i *ᵥ x)).mp hterm
  have hSG : S i * G i = P := by
    simpa only [G, P] using (hS i).self_mul_supportInvSqrt_sq
  have hPr : P *ᵥ (b i - S i *ᵥ x) = 0 := by
    calc
      P *ᵥ (b i - S i *ᵥ x) =
          (S i * G i) *ᵥ (b i - S i *ᵥ x) := by rw [hSG]
      _ = S i *ᵥ (G i *ᵥ (b i - S i *ᵥ x)) :=
        (Matrix.mulVec_mulVec (b i - S i *ᵥ x) (S i) (G i)).symm
      _ = 0 := by rw [hGr, Matrix.mulVec_zero]
  have hPrSelf : P *ᵥ (b i - S i *ᵥ x) = b i - S i *ᵥ x := by
    rw [mulVec_sub, show P *ᵥ b i = b i from hb i]
    rw [mulVec_mulVec, show P * S i = S i from
      (hS i).isHermitian.supportProj_mul_self]
  have hr : b i - S i *ᵥ x = 0 := hPrSelf ▸ hPr
  have hbS : b i = S i *ᵥ x := sub_eq_zero.mp hr
  change G i *ᵥ b i = P *ᵥ x
  have hGS : G i * S i = P := by
    simpa only [G, P] using (hS i).supportInvSqrt_sq_mul_self
  rw [hbS, mulVec_mulVec, hGS]

end Matrix
