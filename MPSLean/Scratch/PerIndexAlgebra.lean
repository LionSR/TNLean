/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.PosDef

/-!
# Part A algebraic identity for `per_index_from_eigenvector`

## Overview

This file develops the algebraic core needed for Sorry 2 (`per_index_from_eigenvector`).

### Key matrix identity (RR† version)

  **`∑ R_i R_i† = ∑ C_i C_i† + ∑ B_i B_i† - 2I`**

### Trace identity

  **`tr(∑ R_i† R_i) = tr(∑ C_i† C_i) - D`**

### Proof structure

1. `∑ R_i† R_i` is PSD — automatic.
2. `tr(∑ R_i† R_i) = tr(∑ C_i† C_i) - D` — `trace_residual_eq`.
3. `tr(∑ C_i† C_i) = D` — **Part B**.
4. PSD + trace 0 → zero — `posSemidef_trace_eq_zero`.
5. `∑ R_i† R_i = 0 → each R_i = 0` — `each_zero_of_sum_conjTranspose_mul_self_zero`.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

namespace PerIndexAlgebra

variable {d D : ℕ}

/-! ## Auxiliary lemmas -/

private lemma star_mul_self_of_norm_one {μ : ℂ} (hmu : ‖μ‖ = 1) :
    star μ * μ = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simp [Complex.normSq_eq_norm_sq, hmu]

lemma sum_swap_conjTranspose (C B : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∑ i, B i * (C i)ᴴ = (∑ i, C i * (B i)ᴴ)ᴴ := by
  rw [Matrix.conjTranspose_sum]
  congr 1; ext i
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

private lemma each_zero_of_sum_conjTranspose_mul_self_zero
    (R : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h : ∑ i : Fin d, (R i)ᴴ * R i = 0) :
    ∀ i : Fin d, R i = 0 := by
  intro i
  have h_psd_i := Matrix.posSemidef_conjTranspose_mul_self (R i)
  have h_each_nonneg : ∀ j, 0 ≤ ((R j)ᴴ * R j).trace.re :=
    fun j => (Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self (R j)).trace_nonneg).1
  have h_tr_sum_re : (∑ j : Fin d, ((R j)ᴴ * R j).trace.re) = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, h]; simp
  have h_tr_re : ((R i)ᴴ * R i).trace.re = 0 :=
    le_antisymm
      (by linarith [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_each_nonneg j)
            |>.mp h_tr_sum_re i (Finset.mem_univ i)])
      (h_each_nonneg i)
  have h_tr_zero : ((R i)ᴴ * R i).trace = 0 :=
    Complex.ext h_tr_re (Complex.le_def.mp h_psd_i.trace_nonneg).2.symm
  exact Matrix.conjTranspose_mul_self_eq_zero.mp (h_psd_i.trace_eq_zero_iff.mp h_tr_zero)

/-! ## Matrix identity for the RR† form -/

set_option maxHeartbeats 800000 in
theorem sum_residual_mul_conjTranspose
    (C B : Fin d → Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hCB : ∑ i : Fin d, C i * (B i)ᴴ = μ • (1 : Matrix (Fin D) (Fin D) ℂ))
    (hmu : ‖μ‖ = 1) :
    let R := fun i => starRingEnd ℂ μ • C i - B i
    ∑ i : Fin d, R i * (R i)ᴴ =
      (∑ i, C i * (C i)ᴴ) + (∑ i, B i * (B i)ᴴ)
      - 2 • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  intro R
  have hmu_sq : star μ * μ = 1 := star_mul_self_of_norm_one hmu
  have hmu_sq' : μ * star μ = 1 := by rw [mul_comm]; exact hmu_sq
  have hBC : ∑ i, B i * (C i)ᴴ = star μ • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [sum_swap_conjTranspose, hCB, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  -- Expand each R_i R_i†
  have expand : ∀ i, R i * (R i)ᴴ =
      C i * (C i)ᴴ
      - star μ • (C i * (B i)ᴴ)
      - μ • (B i * (C i)ᴴ)
      + B i * (B i)ᴴ := by
    intro i
    simp only [R, starRingEnd_apply]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_star]
    -- Expand (star μ • C - B)(μ • C† - B†)
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    -- star μ • C * (μ • C†) = CC†
    have leading : star μ • C i * (μ • (C i)ᴴ) = C i * (C i)ᴴ := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hmu_sq, one_smul]
    rw [leading, Matrix.smul_mul, Matrix.mul_smul]
    -- Now we have: CC† - CB† - (μ • BC† - BB†) where the smul structure needs work
    -- Goal should be an additive identity. Let's use `abel` or `module`
    abel
  simp_rw [expand]
  -- Rewrite as sum of (CC† + BB†) + sum of cross terms
  -- First split into additive + subtractive parts
  conv_lhs =>
    arg 2; ext i
    rw [show C i * (C i)ᴴ - star μ • (C i * (B i)ᴴ) - μ • (B i * (C i)ᴴ) + B i * (B i)ᴴ =
      (C i * (C i)ᴴ + B i * (B i)ᴴ) +
      (-(star μ • (C i * (B i)ᴴ)) + -(μ • (B i * (C i)ᴴ))) from by abel]
  rw [Finset.sum_add_distrib]
  -- Distribute the "diagonal" sum
  conv_lhs =>
    arg 1; rw [show ∑ i : Fin d, (C i * (C i)ᴴ + B i * (B i)ᴴ) =
      (∑ i, C i * (C i)ᴴ) + (∑ i, B i * (B i)ᴴ) from Finset.sum_add_distrib]
  -- Simplify the cross-term sum
  have cross : ∑ x : Fin d, (-(star μ • (C x * (B x)ᴴ)) + -(μ • (B x * (C x)ᴴ))) =
      -(star μ • ∑ x, C x * (B x)ᴴ) + -(μ • ∑ x, B x * (C x)ᴴ) := by
    rw [Finset.sum_add_distrib]; congr 1
    · rw [Finset.sum_neg_distrib, ← Finset.smul_sum]
    · rw [Finset.sum_neg_distrib, ← Finset.smul_sum]
  rw [cross, hCB, hBC, smul_smul, smul_smul, hmu_sq, hmu_sq']
  simp only [one_smul]
  abel

/-! ## Trace identity for ∑ R_i† R_i -/

theorem trace_residual_eq
    (C B : Fin d → Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hCB : ∑ i : Fin d, C i * (B i)ᴴ = μ • (1 : Matrix (Fin D) (Fin D) ℂ))
    (hBB : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hmu : ‖μ‖ = 1) :
    let R := fun i => starRingEnd ℂ μ • C i - B i
    (∑ i : Fin d, (R i)ᴴ * R i).trace =
      (∑ i : Fin d, (C i)ᴴ * C i).trace - ↑D := by
  intro R
  have h_cycle : (∑ i, (R i)ᴴ * R i).trace = (∑ i, R i * (R i)ᴴ).trace := by
    simp_rw [Matrix.trace_sum]
    exact Finset.sum_congr rfl fun i _ => Matrix.trace_mul_comm _ _
  rw [h_cycle, sum_residual_mul_conjTranspose C B μ hCB hmu]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin]
  have h_CC : (∑ i, C i * (C i)ᴴ).trace = (∑ i, (C i)ᴴ * C i).trace := by
    simp_rw [Matrix.trace_sum]
    exact Finset.sum_congr rfl fun i _ => Matrix.trace_mul_comm _ _
  have h_BB : (∑ i, B i * (B i)ᴴ).trace = (↑D : ℂ) := by
    have : (∑ i, B i * (B i)ᴴ).trace = (∑ i, (B i)ᴴ * B i).trace := by
      simp_rw [Matrix.trace_sum]
      exact Finset.sum_congr rfl fun i _ => Matrix.trace_mul_comm _ _
    rw [this, hBB, Matrix.trace_one, Fintype.card_fin]
  rw [h_CC, h_BB]; ring

/-! ## PSD trace zero implies zero -/

theorem posSemidef_trace_eq_zero
    (M : Matrix (Fin D) (Fin D) ℂ) (hpsd : M.PosSemidef)
    (htr : M.trace = 0) : M = 0 :=
  hpsd.trace_eq_zero_iff.mp htr

/-! ## Assembly: closing per_index_from_eigenvector modulo Part B -/

theorem per_index_from_algebraic_identity
    (C B : Fin d → Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hCB : ∑ i : Fin d, C i * (B i)ᴴ = μ • (1 : Matrix (Fin D) (Fin D) ℂ))
    (hBB : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hmu : ‖μ‖ = 1)
    (htr_CC : (∑ i : Fin d, (C i)ᴴ * C i).trace = ↑D) :
    ∀ i : Fin d, B i = starRingEnd ℂ μ • C i := by
  set R := fun i => starRingEnd ℂ μ • C i - B i with hR_def
  have h_psd : (∑ i, (R i)ᴴ * R i).PosSemidef :=
    Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_conjTranspose_mul_self _
  have h_tr : (∑ i, (R i)ᴴ * R i).trace = 0 := by
    rw [trace_residual_eq C B μ hCB hBB hmu, htr_CC, sub_self]
  have h_sum_zero : ∑ i, (R i)ᴴ * R i = 0 := posSemidef_trace_eq_zero _ h_psd h_tr
  have h_each_zero := each_zero_of_sum_conjTranspose_mul_self_zero R h_sum_zero
  intro i
  have hi := h_each_zero i
  simp only [R] at hi
  -- hi : starRingEnd ℂ μ • C i - B i = 0
  -- Therefore B i = starRingEnd ℂ μ • C i
  rw [sub_eq_zero] at hi
  exact hi.symm

end PerIndexAlgebra
