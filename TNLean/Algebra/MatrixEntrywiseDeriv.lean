/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Entrywise derivatives of complex matrix families

A family `P : ℝ → Matrix m n ℂ` of finite matrices is differentiated
entry by entry, without fixing a matrix norm. This file records the
product rule, the trace, differentiability of the determinant and of the
inverse at a nonsingular point (Cramer's rule), and the first-order
quotient rule: if `R = L P` near `t` with `P t = 1`, then `L` is
differentiable at `t` with derivative `R' - L t P'`.

## Main results

* `Matrix.differentiableAt_det_of_entries`,
  `Matrix.differentiableAt_inv_of_entries`: the determinant, and every entry
  of the inverse at a nonsingular point, of an entrywise differentiable
  family are differentiable.
* `Matrix.hasDerivAt_mul_entries`: the entrywise product rule.
* `Matrix.hasDerivAt_entries_of_eventually_eq_mul`: the first-order quotient
  rule.
-/

open Filter Topology
open scoped Matrix BigOperators

namespace Matrix

variable {l m n : Type*} [Fintype m] [Fintype n] {t : ℝ}

omit [Fintype n] in
/-- The entrywise product rule for matrix families. -/
theorem hasDerivAt_mul_entries {F : ℝ → Matrix l m ℂ} {G : ℝ → Matrix m n ℂ}
    {F' : Matrix l m ℂ} {G' : Matrix m n ℂ}
    (hF : ∀ i j, HasDerivAt (fun s ↦ F s i j) (F' i j) t)
    (hG : ∀ i j, HasDerivAt (fun s ↦ G s i j) (G' i j) t) (i : l) (j : n) :
    HasDerivAt (fun s ↦ (F s * G s) i j) ((F' * G t + F t * G') i j) t := by
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ ↦ (hF i k).mul (hG k j)

/-- The trace of an entrywise differentiable family of square matrices. -/
theorem hasDerivAt_trace_of_entries {F : ℝ → Matrix n n ℂ} {F' : Matrix n n ℂ}
    (hF : ∀ i j, HasDerivAt (fun s ↦ F s i j) (F' i j) t) :
    HasDerivAt (fun s ↦ (F s).trace) F'.trace t := by
  simp only [Matrix.trace, Matrix.diag]
  exact HasDerivAt.fun_sum fun k _ ↦ hF k k

variable [DecidableEq n]

/-- The determinant of an entrywise differentiable family is differentiable. -/
theorem differentiableAt_det_of_entries {P : ℝ → Matrix n n ℂ}
    (h : ∀ i j, DifferentiableAt ℝ (fun s ↦ P s i j) t) :
    DifferentiableAt ℝ (fun s ↦ (P s).det) t := by
  simp only [Matrix.det_apply, Units.smul_def]
  refine DifferentiableAt.fun_sum fun σ _ ↦ ?_
  have : DifferentiableAt ℝ (fun s ↦ ∏ i, P s (σ i) i) t :=
    DifferentiableAt.fun_finsetProd fun i _ ↦ h _ _
  simpa only [zsmul_eq_mul] using this.const_mul ((σ.sign : ℤ) : ℂ)

/-- Cramer's rule: at a nonsingular point, every entry of the inverse of an
entrywise differentiable family is differentiable. -/
theorem differentiableAt_inv_of_entries {P : ℝ → Matrix n n ℂ}
    (h : ∀ i j, DifferentiableAt ℝ (fun s ↦ P s i j) t) (hP : (P t).det ≠ 0) (i j : n) :
    DifferentiableAt ℝ (fun s ↦ (P s)⁻¹ i j) t := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((differentiableAt_det_of_entries h).inv hP).mul
    (differentiableAt_det_of_entries fun k l ↦ ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact h k l

/-- **First-order quotient rule.** If `R = L P` near `t`, with `P t = 1`, and
`R` and `P` are entrywise differentiable at `t`, then `L` is entrywise
differentiable at `t` with derivative `R' - L t P'`. -/
theorem hasDerivAt_entries_of_eventually_eq_mul {κ : Type*}
    {L R : ℝ → Matrix κ n ℂ} {P : ℝ → Matrix n n ℂ} {R' : Matrix κ n ℂ} {P' : Matrix n n ℂ}
    (hRP : ∀ᶠ s in 𝓝 t, R s = L s * P s) (hP₁ : P t = 1)
    (hR : ∀ i j, HasDerivAt (fun s ↦ R s i j) (R' i j) t)
    (hP : ∀ i j, HasDerivAt (fun s ↦ P s i j) (P' i j) t) (i : κ) (j : n) :
    HasDerivAt (fun s ↦ L s i j) ((R' - L t * P') i j) t := by
  have hdet : ∀ᶠ s in 𝓝 t, (P s).det ≠ 0 := by
    have hc := (differentiableAt_det_of_entries fun i j ↦ (hP i j).differentiableAt).continuousAt
    refine hc.eventually_ne ?_
    simp [hP₁]
  have hLeq : ∀ᶠ s in 𝓝 t, L s = R s * (P s)⁻¹ := by
    filter_upwards [hRP, hdet] with s hs hd
    rw [hs, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 hd)]
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun s ↦ L s i j) t := by
    intro i j
    refine DifferentiableAt.congr_of_eventuallyEq ?_
      (hLeq.mono fun s hs ↦ congrFun (congrFun hs i) j)
    simp only [Matrix.mul_apply]
    refine DifferentiableAt.fun_sum fun k _ ↦ (hR i k).differentiableAt.mul ?_
    exact differentiableAt_inv_of_entries (fun k l ↦ (hP k l).differentiableAt)
      (by simp [hP₁]) k j
  have hprod : HasDerivAt (fun s ↦ R s i j)
      (∑ k, (deriv (fun s ↦ L s i k) t * P t k j + L t i k * P' k j)) t := by
    refine HasDerivAt.congr_of_eventuallyEq ?_
      (hRP.mono fun s hs ↦ congrFun (congrFun hs i) j)
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ ↦ (hdiff i k).hasDerivAt.mul (hP k j)
  have huniq := (hR i j).unique hprod
  simp only [hP₁, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at huniq
  have : (R' - L t * P') i j = deriv (fun s ↦ L s i j) t := by
    rw [Matrix.sub_apply, Matrix.mul_apply, huniq]; ring
  rw [this]
  exact (hdiff i j).hasDerivAt

end Matrix
