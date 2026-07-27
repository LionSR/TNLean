/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.RelativeEntropySupportLeftRightQuadratic
import TNLean.Channel.Schwarz.SupportRelativeModular
import TNLean.Channel.Schwarz.SupportResolvent

/-!
# Finite-family support defects

This file proves nonnegativity of the fixed-parameter source-\(A\) and
source-\(B\) defects for finite families of positive-semidefinite pairs.
The source-\(A\) statement assumes the kernel inclusion
\(\ker B_i\subseteq\ker A_i\); the source-\(B\) statement needs no kernel
inclusion.

## Main results

* `Matrix.supportSourceBQuadratic_sum_sub_nonneg`: the sum of the source-\(B\)
  support quadratic forms dominates the quadratic form of the summed pair.
* `Matrix.supportLeftRightSupportInv_mulVec_sourceB_eq_of_defect_eq_zero`:
  zero source-\(B\) defect gives the common support-generalized-inverse
  solution for every summand.
* `Matrix.rawSupportSourceAQuadratic_sum_sub_nonneg`: under the kernel
  inclusions, the analogous inequality holds for the unprojected
  source-\(A\) quadratic forms.

## References

* A. Jenčová and M. B. Ruskai, arXiv:0903.2895v4, generalized-inverse
  notation at lines 254--262 and the positive-definite Appendix calculation
  `(Mj)`, `(eq:Schz1)`, and `(eq:Schwzt)` at lines 1313--1343.

This file also proves the fixed-parameter common generalized-inverse solution
from vanishing source-\(B\) defect. The entropy-equality and projected
relative-modular conclusions are assembled downstream; the later recovery
steps are recorded in
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

private theorem supportLeftRight_sourceA_mem_support
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    let hS := supportLeftRightSuperoperator_posSemidef hA hB ht.le
    hS.isHermitian.supportProj *ᵥ
        vec (A * hB.isHermitian.supportProj)ᵀ =
      vec (A * hB.isHermitian.supportProj)ᵀ := by
  classical
  dsimp only
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    if 0 < β j then
      (α i / (α i + t * β j) : ℂ) * W i j
    else 0
  let X := UA * Y * star UB
  have hsolution :
      A * X + t • (X * B) = A * hB.isHermitian.supportProj := by
    simpa only [UA, UB, α, β, W, Y, X] using
      supportLeftRight_sourceA_solution hA hB ht
  have hvec :
      supportLeftRightSuperoperator A B t *ᵥ vec Xᵀ =
        vec (A * hB.isHermitian.supportProj)ᵀ := by
    change
      (A ⊗ₖ (1 : Matrix n n ℂ) +
        t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)) *ᵥ vec Xᵀ =
          vec (A * hB.isHermitian.supportProj)ᵀ
    rw [leftRight_mulVec_vec_transpose, hsolution]
  rw [← hvec, Matrix.mulVec_mulVec]
  exact congrArg (fun M : Matrix (n × n) (n × n) ℂ ↦ M *ᵥ vec Xᵀ)
    (supportLeftRightSuperoperator_posSemidef hA hB
      ht.le).isHermitian.supportProj_mul_self

omit [Fintype n] in
private theorem sum_supportLeftRightSuperoperator
    {ι : Type*} [Fintype ι]
    (A B : ι → Matrix n n ℂ) (t : ℝ) :
    ∑ i, supportLeftRightSuperoperator (A i) (B i) t =
      supportLeftRightSuperoperator (∑ i, A i) (∑ i, B i) t := by
  ext ⟨p, q⟩ ⟨r, s⟩
  simp [supportLeftRightSuperoperator, Matrix.sum_apply,
    Complex.real_smul, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]

omit [Fintype n] [DecidableEq n] in
private theorem sum_vec_transpose
    {ι : Type*} [Fintype ι] (B : ι → Matrix n n ℂ) :
    ∑ i, vec (B i)ᵀ = vec (∑ i, B i)ᵀ := by
  ext ⟨p, q⟩
  simp [Matrix.vec, Matrix.sum_apply]

private theorem supportLeftRight_sourceB_family_mem_support
    {ι : Type*} [Fintype ι]
    (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    let S : ι → Matrix (n × n) (n × n) ℂ :=
      fun i ↦ supportLeftRightSuperoperator (A i) (B i) t
    let b : ι → n × n → ℂ := fun i ↦ vec (B i)ᵀ
    let hS : ∀ i, (S i).PosSemidef :=
      fun i ↦ supportLeftRightSuperoperator_posSemidef
        (hA i) (hB i) ht.le
    (∀ i, (hS i).isHermitian.supportProj *ᵥ b i = b i) ∧
      (let Sbar := ∑ i, S i
       let bbar := ∑ i, b i
       let hSbar : Sbar.PosSemidef :=
         Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
       hSbar.isHermitian.supportProj *ᵥ bbar = bbar) := by
  classical
  dsimp only
  constructor
  · intro i
    exact supportLeftRight_sourceB_mem_support (hA i) (hB i) ht
  · let Abar : Matrix n n ℂ := ∑ i, A i
    let Bbar : Matrix n n ℂ := ∑ i, B i
    let hAbar : Abar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
    let hBbar : Bbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
    have htransport
        (Sbar : Matrix (n × n) (n × n) ℂ) (bbar : n × n → ℂ)
        (hSbar : Sbar.PosSemidef)
        (hSbar_eq : Sbar = supportLeftRightSuperoperator Abar Bbar t)
        (hbbar_eq : bbar = vec Bbarᵀ) :
        hSbar.isHermitian.supportProj *ᵥ bbar = bbar := by
      subst Sbar
      subst bbar
      exact supportLeftRight_sourceB_mem_support hAbar hBbar ht
    exact htransport
      (∑ i, supportLeftRightSuperoperator (A i) (B i) t)
      (∑ i, vec (B i)ᵀ)
      (Matrix.posSemidef_sum Finset.univ fun i _ ↦
        supportLeftRightSuperoperator_posSemidef (hA i) (hB i) ht.le)
      (by simpa only [Abar, Bbar] using
        sum_supportLeftRightSuperoperator A B t)
      (by simpa only [Bbar] using sum_vec_transpose B)

private theorem supportSourceB_defect_eq_supportResolvent_defect_re
    {ι : Type*} [Fintype ι]
    (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    let Abar := ∑ i, A i
    let Bbar := ∑ i, B i
    let hAbar : Abar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
    let hBbar : Bbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
    let S : ι → Matrix (n × n) (n × n) ℂ :=
      fun i ↦ supportLeftRightSuperoperator (A i) (B i) t
    let b : ι → n × n → ℂ := fun i ↦ vec (B i)ᵀ
    let hS : ∀ i, (S i).PosSemidef :=
      fun i ↦ supportLeftRightSuperoperator_posSemidef
        (hA i) (hB i) ht.le
    let Sbar := ∑ i, S i
    let bbar := ∑ i, b i
    let hSbar : Sbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
    (∑ i, supportSourceBQuadratic (hA i) (hB i) t) -
        supportSourceBQuadratic hAbar hBbar t =
      ((∑ i, dotProduct (star (b i))
          ((hS i).supportInv *ᵥ b i)) -
        dotProduct (star bbar) (hSbar.supportInv *ᵥ bbar)).re := by
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
    fun i ↦ supportLeftRightSuperoperator_posSemidef
      (hA i) (hB i) ht.le
  let Sbar : Matrix (n × n) (n × n) ℂ := ∑ i, S i
  let bbar : n × n → ℂ := ∑ i, b i
  let hSbar : Sbar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
  have hQi (i : ι) :
      supportSourceBQuadratic (hA i) (hB i) t =
        (dotProduct (star (b i)) ((hS i).supportInv *ᵥ b i)).re := by
    rw [supportSourceBQuadratic,
      supportLeftRightSupportInv_eq (hA i) (hB i) ht.le]
  have hQsum :
      ∑ i, supportSourceBQuadratic (hA i) (hB i) t =
        (∑ i, dotProduct (star (b i))
          ((hS i).supportInv *ᵥ b i)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hQi i
  have hQbar :
      supportSourceBQuadratic hAbar hBbar t =
        (dotProduct (star bbar) (hSbar.supportInv *ᵥ bbar)).re := by
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
    exact htransport Sbar bbar hSbar
      (by simpa only [S, Abar, Bbar] using
        sum_supportLeftRightSuperoperator A B t)
      (by simpa only [b, Bbar] using sum_vec_transpose B)
  rw [hQsum, hQbar, Complex.sub_re]

private theorem supportLeftRight_sourceB_common_supportInv
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    {t : ℝ} (ht : 0 < t)
    (hzero :
      let Abar := ∑ i, A i
      let Bbar := ∑ i, B i
      let hAbar : Abar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
      let hBbar : Bbar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
      (∑ i, supportSourceBQuadratic (hA i) (hB i) t) -
        supportSourceBQuadratic hAbar hBbar t = 0) :
    let S : ι → Matrix (n × n) (n × n) ℂ :=
      fun i ↦ supportLeftRightSuperoperator (A i) (B i) t
    let b : ι → n × n → ℂ := fun i ↦ vec (B i)ᵀ
    let hS : ∀ i, (S i).PosSemidef :=
      fun i ↦ supportLeftRightSuperoperator_posSemidef
        (hA i) (hB i) ht.le
    let Sbar := ∑ i, S i
    let bbar := ∑ i, b i
    let hSbar : Sbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
    ∀ i,
      (hS i).supportInv *ᵥ b i =
        (hS i).isHermitian.supportProj *ᵥ
          (hSbar.supportInv *ᵥ bbar) := by
  classical
  dsimp only
  let S : ι → Matrix (n × n) (n × n) ℂ :=
    fun i ↦ supportLeftRightSuperoperator (A i) (B i) t
  let b : ι → n × n → ℂ := fun i ↦ vec (B i)ᵀ
  let hS : ∀ i, (S i).PosSemidef :=
    fun i ↦ supportLeftRightSuperoperator_posSemidef
      (hA i) (hB i) ht.le
  have hb : ∀ i, (hS i).isHermitian.supportProj *ᵥ b i = b i := by
    simpa only [S, b, hS] using
      (supportLeftRight_sourceB_family_mem_support A B hA hB ht).1
  have hbar :
      let Sbar := ∑ i, S i
      let bbar := ∑ i, b i
      let hSbar : Sbar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
      hSbar.isHermitian.supportProj *ᵥ bbar = bbar := by
    simpa only [S, b, hS] using
      (supportLeftRight_sourceB_family_mem_support A B hA hB ht).2
  have hdefect_re :
      let Sbar := ∑ i, S i
      let bbar := ∑ i, b i
      let hSbar : Sbar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
      ((∑ i, dotProduct (star (b i))
          ((hS i).supportInv *ᵥ b i)) -
        dotProduct (star bbar) (hSbar.supportInv *ᵥ bbar)).re = 0 := by
    simpa only [S, b, hS] using
      (supportSourceB_defect_eq_supportResolvent_defect_re
        A B hA hB ht).symm.trans hzero
  simpa only [PosSemidef.supportInv] using
    support_resolvent_eq_of_defect_eq_zero S b hS hb hbar
      (by simpa only [PosSemidef.supportInv] using hdefect_re)

private theorem sum_supportInv_mulVec_sourceB_eq
    {ι : Type*} [Fintype ι]
    (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    let Abar := ∑ i, A i
    let Bbar := ∑ i, B i
    let hAbar : Abar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
    let hBbar : Bbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
    let S : ι → Matrix (n × n) (n × n) ℂ :=
      fun i ↦ supportLeftRightSuperoperator (A i) (B i) t
    let b : ι → n × n → ℂ := fun i ↦ vec (B i)ᵀ
    let hS : ∀ i, (S i).PosSemidef :=
      fun i ↦ supportLeftRightSuperoperator_posSemidef
        (hA i) (hB i) ht.le
    let Sbar := ∑ i, S i
    let bbar := ∑ i, b i
    let hSbar : Sbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
    hSbar.supportInv *ᵥ bbar =
      supportLeftRightSupportInv hAbar hBbar t *ᵥ vec Bbarᵀ := by
  classical
  dsimp only
  rw [supportLeftRightSupportInv_eq _ _ ht.le]
  have htransport
      (Sbar : Matrix (n × n) (n × n) ℂ) (bbar : n × n → ℂ)
      (hSbar : Sbar.PosSemidef)
      (hSbar_eq :
        Sbar = supportLeftRightSuperoperator (∑ i, A i) (∑ i, B i) t)
      (hbbar_eq : bbar = vec (∑ i, B i)ᵀ) :
      hSbar.supportInv *ᵥ bbar =
        (supportLeftRightSuperoperator_posSemidef
          (Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i)
          (Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i)
          ht.le).supportInv *ᵥ vec (∑ i, B i)ᵀ := by
    subst Sbar
    subst bbar
    rfl
  exact htransport
    (∑ i, supportLeftRightSuperoperator (A i) (B i) t)
    (∑ i, vec (B i)ᵀ)
    (Matrix.posSemidef_sum Finset.univ fun i _ ↦
      supportLeftRightSuperoperator_posSemidef (hA i) (hB i) ht.le)
    (sum_supportLeftRightSuperoperator A B t)
    (sum_vec_transpose B)

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
`(eq:Schwzt)` at lines 1313--1343, using their generalized-inverse notation
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
  let S : ι → Matrix (n × n) (n × n) ℂ :=
    fun i ↦ supportLeftRightSuperoperator (A i) (B i) t
  let b : ι → n × n → ℂ := fun i ↦ vec (B i)ᵀ
  let hS : ∀ i, (S i).PosSemidef :=
    fun i ↦ supportLeftRightSuperoperator_posSemidef (hA i) (hB i) ht.le
  have hb : ∀ i, (hS i).isHermitian.supportProj *ᵥ b i = b i := by
    simpa only [S, b, hS] using
      (supportLeftRight_sourceB_family_mem_support A B hA hB ht).1
  have hbar :
      let Sbar := ∑ i, S i
      let bbar := ∑ i, b i
      let hSbar : Sbar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
      hSbar.isHermitian.supportProj *ᵥ bbar = bbar := by
    simpa only [S, b, hS] using
      (supportLeftRight_sourceB_family_mem_support A B hA hB ht).2
  have hdefect_re :
      let Sbar := ∑ i, S i
      let bbar := ∑ i, b i
      let hSbar : Sbar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
      0 ≤ ((∑ i, dotProduct (star (b i))
          ((hS i).supportInv *ᵥ b i)) -
        dotProduct (star bbar) (hSbar.supportInv *ᵥ bbar)).re := by
    simpa only [PosSemidef.supportInv] using
      support_resolvent_quadratic_sum_sub_nonneg S b hS hb hbar
  rw [supportSourceB_defect_eq_supportResolvent_defect_re A B hA hB ht]
  simpa only [S, b, hS] using hdefect_re

/-- For a finite nonempty family of positive-semidefinite pairs and a fixed
\(t>0\), vanishing of the real source-\(B\) defect makes every local
support-generalized-inverse solution the restriction of the summed solution:
\[
  S_i^+\operatorname{vec}(B_i^{\mathsf T})
  =
  P_{S_i}S_\Sigma^+\operatorname{vec}(B_\Sigma^{\mathsf T}).
\]

This is the fixed-parameter residual step behind `(basiceq)` in
Jenčová--Ruskai, arXiv:0903.2895v4, lines 652--660 and 788--790. The theorem
needs no kernel inclusion between \(B_i\) and \(A_i\); that hypothesis enters
the preceding entropy-equality argument. This statement stops before
identifying the restrictions with the common projected relative-modular
resolvent. -/
theorem supportLeftRightSupportInv_mulVec_sourceB_eq_of_defect_eq_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    {t : ℝ} (ht : 0 < t)
    (hzero :
      let Abar := ∑ i, A i
      let Bbar := ∑ i, B i
      let hAbar : Abar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
      let hBbar : Bbar.PosSemidef :=
        Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
      (∑ i, supportSourceBQuadratic (hA i) (hB i) t) -
        supportSourceBQuadratic hAbar hBbar t = 0) :
    let Abar := ∑ i, A i
    let Bbar := ∑ i, B i
    let hAbar : Abar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
    let hBbar : Bbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
    ∀ i,
      supportLeftRightSupportInv (hA i) (hB i) t *ᵥ vec (B i)ᵀ =
        (supportLeftRightSuperoperator_posSemidef
          (hA i) (hB i) ht.le).isHermitian.supportProj *ᵥ
          (supportLeftRightSupportInv hAbar hBbar t *ᵥ vec Bbarᵀ) := by
  classical
  dsimp only
  let Abar : Matrix n n ℂ := ∑ i, A i
  let Bbar : Matrix n n ℂ := ∑ i, B i
  let hAbar : Abar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
  let hBbar : Bbar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
  have hcommon :=
    supportLeftRight_sourceB_common_supportInv A B hA hB ht hzero
  have haggregate :=
    sum_supportInv_mulVec_sourceB_eq A B hA hB ht
  intro i
  rw [supportLeftRightSupportInv_eq (hA i) (hB i) ht.le]
  rw [← haggregate]
  exact hcommon i

/-- For a positive-semidefinite family, the right-support projection of each
summand absorbs the right-support projection of the sum:
\[
  (1\otimes P_{B_i}^{\mathsf T})
  (1\otimes P_{\sum_j B_j}^{\mathsf T})
  =1\otimes P_{B_i}^{\mathsf T}.
\]

This records the support restriction used for each summand in the singular
family argument of Jenčová--Ruskai, arXiv:0903.2895v4, lines 766--790. -/
theorem supportRightProj_mul_sumSupportRightProj_eq
    {ι : Type*} [Fintype ι]
    (B : ι → Matrix n n ℂ) (hB : ∀ i, (B i).PosSemidef)
    (i : ι) :
    let Bbar := ∑ j, B j
    let hBbar : Bbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun j _ ↦ hB j
    ((1 : Matrix n n ℂ) ⊗ₖ (hB i).isHermitian.supportProjᵀ) *
        ((1 : Matrix n n ℂ) ⊗ₖ hBbar.isHermitian.supportProjᵀ) =
      (1 : Matrix n n ℂ) ⊗ₖ (hB i).isHermitian.supportProjᵀ := by
  classical
  dsimp only
  let Bbar : Matrix n n ℂ := ∑ j, B j
  let hBbar : Bbar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun j _ ↦ hB j
  have hker :
      ∀ v : n → ℂ, Bbar *ᵥ v = 0 →
        (hB i).isHermitian.supportProj *ᵥ v = 0 := by
    intro v hv
    apply (hB i).supportProj_mulVec_eq_zero_of_mulVec_eq_zero
    exact Matrix.PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero hB
      (by simpa only [Bbar] using hv) i
  have hPiPbar :
      (hB i).isHermitian.supportProj *
          hBbar.isHermitian.supportProj =
        (hB i).isHermitian.supportProj :=
    hBbar.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hker
  have hPbarPi :
      hBbar.isHermitian.supportProj *
          (hB i).isHermitian.supportProj =
        (hB i).isHermitian.supportProj := by
    have hstar := congrArg Matrix.conjTranspose hPiPbar
    simpa only [Matrix.conjTranspose_mul,
      hBbar.isHermitian.supportProj_isHermitian.eq,
      (hB i).isHermitian.supportProj_isHermitian.eq] using hstar
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
    ← Matrix.transpose_mul, hPbarPi]

/-- For a finite nonempty family of positive-semidefinite pairs satisfying
\(\ker B_i\subseteq\ker A_i\), and for \(t>0\), the sum of the raw
source-\(A\) support quadratic forms dominates the quadratic form of the
summed pair:
\[
  0\leq \sum_i Q^A_{A_i,B_i}(t)
    -Q^A_{\sum_i A_i,\sum_i B_i}(t).
\]

The kernel inclusions identify the projected sources \(A_iP_{B_i}\) with
\(A_i\), and also give the corresponding inclusion for the summed pair.
This is the source-\(A\) support-domain extension of the positive-definite
residual calculation in Jenčová--Ruskai, arXiv:0903.2895v4, Appendix,
equations `(Mj)`, `(eq:Schz1)`, and `(eq:Schwzt)`. The paper does not state
this fixed-\(t\) extension separately.

This lemma proves only algebraic nonnegativity. It does not derive
vanishing of the defect from equality of relative entropies, a common
support resolvent, or Petz recovery. -/
lemma rawSupportSourceAQuadratic_sum_sub_nonneg
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (hker : ∀ i v, B i *ᵥ v = 0 → A i *ᵥ v = 0)
    {t : ℝ} (ht : 0 < t) :
    let Abar := ∑ i, A i
    let Bbar := ∑ i, B i
    let hAbar : Abar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
    let hBbar : Bbar.PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
    0 ≤ (∑ i, rawSupportSourceAQuadratic (hA i) (hB i) t) -
      rawSupportSourceAQuadratic hAbar hBbar t := by
  classical
  dsimp only
  let Abar : Matrix n n ℂ := ∑ i, A i
  let Bbar : Matrix n n ℂ := ∑ i, B i
  let hAbar : Abar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hA i
  let hBbar : Bbar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hB i
  have hkerbar : ∀ v : n → ℂ, Bbar *ᵥ v = 0 → Abar *ᵥ v = 0 := by
    intro v hv
    have hvsum : (∑ i, B i) *ᵥ v = 0 := by simpa only [Bbar] using hv
    have hBi : ∀ i, B i *ᵥ v = 0 :=
      fun i ↦ Matrix.PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero hB hvsum i
    calc
      Abar *ᵥ v = ∑ i, A i *ᵥ v := by
        simpa only [Abar] using Matrix.sum_mulVec Finset.univ A v
      _ = 0 := Finset.sum_eq_zero fun i _ ↦ hker i v (hBi i)
  let S : ι → Matrix (n × n) (n × n) ℂ :=
    fun i ↦ supportLeftRightSuperoperator (A i) (B i) t
  let b : ι → n × n → ℂ := fun i ↦ vec (A i)ᵀ
  let hS : ∀ i, (S i).PosSemidef :=
    fun i ↦ supportLeftRightSuperoperator_posSemidef (hA i) (hB i) ht.le
  have hb : ∀ i, (hS i).isHermitian.supportProj *ᵥ b i = b i := by
    intro i
    have hAi :
        A i * (hB i).isHermitian.supportProj = A i :=
      (hB i).isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le (hker i)
    simpa only [S, b, hS, hAi] using
      supportLeftRight_sourceA_mem_support (hA i) (hB i) ht
  have hSsum :
      ∑ i, S i = supportLeftRightSuperoperator Abar Bbar t := by
    ext ⟨p, q⟩ ⟨r, s⟩
    simp [S, Abar, Bbar, supportLeftRightSuperoperator,
      Matrix.sum_apply, Complex.real_smul, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum]
  have hbsum : ∑ i, b i = vec Abarᵀ := by
    ext ⟨p, q⟩
    simp [b, Abar, Matrix.vec, Matrix.sum_apply]
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
        (hbbar_eq : bbar = vec Abarᵀ) :
        hSbar.isHermitian.supportProj *ᵥ bbar = bbar := by
      subst Sbar
      subst bbar
      have hAbar_support :
          Abar * hBbar.isHermitian.supportProj = Abar :=
        hBbar.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hkerbar
      simpa only [hAbar_support] using
        supportLeftRight_sourceA_mem_support hAbar hBbar ht
    exact htransport (∑ i, S i) (∑ i, b i)
      (Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i) hSsum hbsum
  let Sbar : Matrix (n × n) (n × n) ℂ := ∑ i, S i
  let bbar : n × n → ℂ := ∑ i, b i
  let hSbar : Sbar.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ ↦ hS i
  let G : ι → Matrix (n × n) (n × n) ℂ := fun i ↦ (hS i).supportInv
  let Gbar : Matrix (n × n) (n × n) ℂ := hSbar.supportInv
  have hdefect_re :
      0 ≤ ((∑ i, dotProduct (star (b i)) (G i *ᵥ b i)) -
        dotProduct (star bbar) (Gbar *ᵥ bbar)).re := by
    simpa only [Sbar, bbar, hSbar, G, Gbar] using
      support_resolvent_quadratic_sum_sub_nonneg S b hS hb hbar
  have hQi (i : ι) :
      rawSupportSourceAQuadratic (hA i) (hB i) t =
        (dotProduct (star (b i)) (G i *ᵥ b i)).re := by
    rw [rawSupportSourceAQuadratic,
      supportLeftRightSupportInv_eq (hA i) (hB i) ht.le]
  have hQsum :
      ∑ i, rawSupportSourceAQuadratic (hA i) (hB i) t =
        (∑ i, dotProduct (star (b i)) (G i *ᵥ b i)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hQi i
  have hQbar :
      rawSupportSourceAQuadratic hAbar hBbar t =
        (dotProduct (star bbar) (Gbar *ᵥ bbar)).re := by
    rw [rawSupportSourceAQuadratic,
      supportLeftRightSupportInv_eq hAbar hBbar ht.le]
    have htransport
        (S' : Matrix (n × n) (n × n) ℂ) (b' : n × n → ℂ)
        (hS' : S'.PosSemidef)
        (hS'_eq : S' = supportLeftRightSuperoperator Abar Bbar t)
        (hb'_eq : b' = vec Abarᵀ) :
        (dotProduct (star (vec Abarᵀ))
          ((supportLeftRightSuperoperator_posSemidef
            hAbar hBbar ht.le).supportInv *ᵥ vec Abarᵀ)).re =
          (dotProduct (star b') (hS'.supportInv *ᵥ b')).re := by
      subst S'
      subst b'
      rfl
    exact htransport Sbar bbar hSbar hSsum hbsum
  rw [hQsum, hQbar]
  simpa only [Complex.sub_re] using hdefect_re

end Matrix
