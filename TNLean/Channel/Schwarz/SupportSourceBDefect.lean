/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.RelativeEntropySupportLeftRightQuadratic
import TNLean.Channel.Schwarz.SupportRelativeModular
import TNLean.Channel.Schwarz.SupportResolvent

/-!
# The finite-family source-B support defect

This file proves nonnegativity of the fixed-parameter source-\(B\) defect for
a finite family of positive-semidefinite pairs. No inclusion between the
kernels of the two matrices in a pair is needed.

## Main result

* `Matrix.supportSourceBQuadratic_sum_sub_nonneg`: the sum of the source-\(B\)
  support quadratic forms dominates the quadratic form of the summed pair.

## References

* A. Jenčová and M. B. Ruskai, arXiv:0903.2895v4, generalized-inverse
  notation at lines 254--262 and the positive-definite Appendix calculation
  `(Mj)`, `(eq:Schz1)`, and `(eq:Schwzt)` at lines 1299--1328.

The subsequent singular entropy-equality argument is not asserted here. Its
remaining steps are recorded in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem supportLeftRight_sourceB_mem_support
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    let hS := supportLeftRightSuperoperator_posSemidef hA hB ht.le
    hS.isHermitian.supportProj *ᵥ vec Bᵀ = vec Bᵀ := by
  dsimp only
  let Bplus := hB.supportInvSqrt * hB.supportInvSqrt
  let delta := A ⊗ₖ Bplusᵀ
  let res := t • (1 : Matrix (n × n) (n × n) ℂ) + delta
  let P := (1 : Matrix n n ℂ) ⊗ₖ hB.isHermitian.supportProjᵀ
  let y := P *ᵥ (res⁻¹ *ᵥ vec (1 : Matrix n n ℂ)ᵀ)
  have hy :
      supportLeftRightSuperoperator A B t *ᵥ y = vec Bᵀ := by
    simpa only [supportLeftRightSuperoperator, Bplus, delta, res, P, y] using
      supportRelativeModular_sourceB_solution hA hB ht
  have hsupport_mul :
      (supportLeftRightSuperoperator_posSemidef hA hB ht.le).isHermitian.supportProj *
          supportLeftRightSuperoperator A B t =
        supportLeftRightSuperoperator A B t :=
    (supportLeftRightSuperoperator_posSemidef hA hB
      ht.le).isHermitian.supportProj_mul_self
  rw [← hy]
  conv_lhs => rw [Matrix.mulVec_mulVec]
  rw [hsupport_mul]

/-- For a finite nonempty family of positive-semidefinite pairs and a fixed
\(t>0\), the sum of the source-\(B\) support quadratic forms dominates the
source-\(B\) quadratic form of the summed pair:
\[
  0\leq \sum_i Q^B_{A_i,B_i}(t)
    -Q^B_{\sum_i A_i,\sum_i B_i}(t).
\]

This is a positive-semidefinite support-domain extension of the
positive-definite residual calculation in Jenčová--Ruskai,
arXiv:0903.2895v4, Appendix, equations `(Mj)`, `(eq:Schz1)`, and
`(eq:Schwzt)` at lines 1299--1328, using their generalized-inverse notation
at lines 254--262. The cited paper does not state this support extension.
Here the source vector \(\operatorname{vec}(B_i^{\mathsf T})\) belongs to the
support of its left-right operator without an assumption
\(\ker B_i\subseteq\ker A_i\). By contrast, the subsequent singular equality
theorem in the paper, at lines 761--785, assumes
\(\ker B_i\subseteq\ker A_i\); that theorem is not asserted here.

This fixed-\(t\) algebraic statement does not assert rigidity, an integral
identity, or a Petz recovery theorem. The surrounding singular
entropy-equality gap is documented in
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`. -/
theorem supportSourceBQuadratic_sum_sub_nonneg
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    let Abar := ∑ i, A i
    let Bbar := ∑ i, B i
    let hAbar : Abar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
    let hBbar : Bbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
    0 ≤ (∑ i, supportSourceBQuadratic (hA i) (hB i) t) -
      supportSourceBQuadratic hAbar hBbar t := by
  classical
  dsimp only
  let Abar : Matrix n n ℂ := ∑ i, A i
  let Bbar : Matrix n n ℂ := ∑ i, B i
  let hAbar : Abar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
  let hBbar : Bbar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
  let S : ι → Matrix (n × n) (n × n) ℂ :=
    fun i ↦ supportLeftRightSuperoperator (A i) (B i) t
  let b : ι → n × n → ℂ := fun i ↦ vec (B i)ᵀ
  let hS : ∀ i, (S i).PosSemidef :=
    fun i ↦ supportLeftRightSuperoperator_posSemidef (hA i) (hB i) ht.le
  have hb : ∀ i, (hS i).isHermitian.supportProj *ᵥ b i = b i := by
    intro i
    simpa only [S, b, hS] using
      supportLeftRight_sourceB_mem_support (hA i) (hB i) ht
  have hSsum :
      ∑ i, S i = supportLeftRightSuperoperator Abar Bbar t := by
    ext ⟨p, q⟩ ⟨r, s⟩
    simp [S, Abar, Bbar, supportLeftRightSuperoperator,
      Matrix.sum_apply, Complex.real_smul, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum]
  have hbsum : ∑ i, b i = vec Bbarᵀ := by
    ext ⟨p, q⟩
    simp [b, Bbar, Matrix.vec, Matrix.sum_apply]
  have hbar :
      let Sbar := ∑ i, S i
      let bbar := ∑ i, b i
      let hSbar : Sbar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
      hSbar.isHermitian.supportProj *ᵥ bbar = bbar := by
    dsimp only
    have htransport
        (Sbar : Matrix (n × n) (n × n) ℂ) (bbar : n × n → ℂ)
        (hSbar : Sbar.PosSemidef)
        (hSbar_eq : Sbar = supportLeftRightSuperoperator Abar Bbar t)
        (hbbar_eq : bbar = vec Bbarᵀ) :
        hSbar.isHermitian.supportProj *ᵥ bbar = bbar := by
      subst Sbar
      subst bbar
      exact supportLeftRight_sourceB_mem_support hAbar hBbar ht
    exact htransport (∑ i, S i) (∑ i, b i)
      (Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i) hSsum hbsum
  let Sbar : Matrix (n × n) (n × n) ℂ := ∑ i, S i
  let bbar : n × n → ℂ := ∑ i, b i
  let hSbar : Sbar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
  let G : ι → Matrix (n × n) (n × n) ℂ := fun i ↦ (hS i).supportInv
  let Gbar : Matrix (n × n) (n × n) ℂ := hSbar.supportInv
  let x : n × n → ℂ := Gbar *ᵥ bbar
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
  have hdefect_re :
      0 ≤ ((∑ i, dotProduct (star (b i)) (G i *ᵥ b i)) -
        dotProduct (star bbar) (Gbar *ᵥ bbar)).re := by
    rw [hres] at hresidual_nonneg
    exact (Complex.nonneg_iff.mp hresidual_nonneg).1
  have hQi (i : ι) :
      supportSourceBQuadratic (hA i) (hB i) t =
        (dotProduct (star (b i)) (G i *ᵥ b i)).re := by
    rw [supportSourceBQuadratic,
      supportLeftRightSupportInv_eq (hA i) (hB i) ht.le]
  have hQsum :
      ∑ i, supportSourceBQuadratic (hA i) (hB i) t =
        (∑ i, dotProduct (star (b i)) (G i *ᵥ b i)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hQi i
  have hQbar :
      supportSourceBQuadratic hAbar hBbar t =
        (dotProduct (star bbar) (Gbar *ᵥ bbar)).re := by
    rw [supportSourceBQuadratic,
      supportLeftRightSupportInv_eq hAbar hBbar ht.le]
    have htransport
        (S' : Matrix (n × n) (n × n) ℂ) (b' : n × n → ℂ)
        (hS' : S'.PosSemidef)
        (hS'_eq : S' = supportLeftRightSuperoperator Abar Bbar t)
        (hb'_eq : b' = vec Bbarᵀ) :
        (dotProduct (star (vec Bbarᵀ))
          ((supportLeftRightSuperoperator_posSemidef
            hAbar hBbar ht.le).supportInv *ᵥ vec Bbarᵀ)).re =
          (dotProduct (star b') (hS'.supportInv *ᵥ b')).re := by
      subst S'
      subst b'
      rfl
    exact htransport Sbar bbar hSbar hSsum hbsum
  rw [hQsum, hQbar]
  simpa only [Complex.sub_re] using hdefect_re

end Matrix
