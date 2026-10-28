/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TraceExpLogConcavity
import Mathlib.Analysis.Convex.Jensen

/-!
# Finite Jensen inequalities for trace exponentials

Lieb's concavity gives Jensen's inequality for a finite uniform Hermitian family.
Iterating it over independent uniform samples bounds the average trace exponential
by the trace exponential of the sum of the logarithmic moment generating functions.

These are finite uniform specializations of Tropp, *User-friendly tail bounds for
sums of random matrices*, Corollary 3.3 and Lemma 3.4:
https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf.
The corresponding assertions for general random matrices are separate results.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder


namespace Matrix

open Classical in
/-- Finite uniform Jensen inequality for the trace exponential, from Tropp, Corollary 3.3. -/
theorem average_trace_exp_add_le_trace_exp_log_average_exp
    {α n : Type*} [Fintype α] [Nonempty α] [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (Y : α → Matrix n n ℂ) (hY : ∀ a, (Y a).IsHermitian) :
    (Fintype.card α : ℝ)⁻¹ * (∑ a, (NormedSpace.exp (H + Y a)).trace.re) ≤
      (NormedSpace.exp (H + CFC.log
        ((Fintype.card α : ℝ)⁻¹ • ∑ a, NormedSpace.exp (Y a)))).trace.re := by
  classical
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmass : ∑ _a : α, (Fintype.card α : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hα]
  have hpos (a : α) : (NormedSpace.exp (Y a)).PosDef := by
    rw [← Matrix.isStrictlyPositive_iff_posDef,
      ← CFC.real_exp_eq_normedSpace_exp (hY a).isSelfAdjoint]
    exact (cfc_isStrictlyPositive_iff Real.exp _ (by fun_prop) (hY a).isSelfAdjoint).mpr
      (fun x _ ↦ Real.exp_pos x)
  have hj := (concaveOn_trace_exp_add_log hH).le_map_sum (t := Finset.univ)
    (w := fun _ ↦ (Fintype.card α : ℝ)⁻¹) (p := fun a ↦ NormedSpace.exp (Y a))
    (fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) hmass (fun a _ ↦ hpos a)
  simpa only [← Finset.smul_sum, ← Finset.mul_sum, CFC.log_exp _ (hY _).isSelfAdjoint,
    smul_eq_mul] using hj

end Matrix

namespace Matrix

open Classical in
/-- Iterated finite uniform Jensen inequality for independent identically distributed samples.
This is the finite uniform specialization of Tropp, Lemma 3.4, allowing a fixed Hermitian shift. -/
theorem sum_trace_exp_iid_le {α n : Type*} [Fintype α] [Nonempty α]
    [Fintype n] [DecidableEq n] (Y : α → Matrix n n ℂ)
    (hY : ∀ a, (Y a).IsHermitian) (m : ℕ) {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (∑ σ : Fin m → α, (NormedSpace.exp (H + ∑ j, Y (σ j))).trace.re) ≤
      (Fintype.card α : ℝ) ^ m *
        (NormedSpace.exp (H + (m : ℝ) • CFC.log
          ((Fintype.card α : ℝ)⁻¹ • ∑ a, NormedSpace.exp (Y a)))).trace.re := by
  classical
  let M : Matrix n n ℂ := (Fintype.card α : ℝ)⁻¹ • ∑ a, NormedSpace.exp (Y a)
  have hC : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  induction m generalizing H with
  | zero => simp
  | succ m ih =>
    have hsplit :
        (∑ σ : Fin (m + 1) → α, (NormedSpace.exp (H + ∑ j, Y (σ j))).trace.re) =
        ∑ τ : Fin m → α, ∑ a : α,
          (NormedSpace.exp ((H + ∑ j, Y (τ j)) + Y a)).trace.re := by
      rw [← (Fin.consEquiv (fun _ : Fin (m + 1) ↦ α)).sum_comp
        (fun σ ↦ (NormedSpace.exp (H + ∑ j, Y (σ j))).trace.re)]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro τ _
      apply Finset.sum_congr rfl
      intro a _
      simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      congr 2
      abel
    have hstep (τ : Fin m → α) :
        (∑ a : α, (NormedSpace.exp ((H + ∑ j, Y (τ j)) + Y a)).trace.re) ≤
        (Fintype.card α : ℝ) *
          (NormedSpace.exp ((H + CFC.log M) + ∑ j, Y (τ j))).trace.re := by
      have hj := average_trace_exp_add_le_trace_exp_log_average_exp
        (hH.add ((isSelfAdjoint_sum Finset.univ fun j _ ↦
          (hY (τ j)).isSelfAdjoint).isHermitian)) Y hY
      have hh := mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg (Fintype.card α))
      have hadd : ((H + ∑ j, Y (τ j)) + CFC.log M) =
          ((H + CFC.log M) + ∑ j, Y (τ j)) := by abel
      change (Fintype.card α : ℝ) * ((Fintype.card α : ℝ)⁻¹ * _) ≤
        (Fintype.card α : ℝ) * (NormedSpace.exp
          ((H + ∑ j, Y (τ j)) + CFC.log M)).trace.re at hh
      rw [hadd] at hh
      simpa only [← mul_assoc, mul_inv_cancel₀ hC, one_mul] using hh
    have hfinal : (H + CFC.log M) + (m : ℝ) • CFC.log M =
        H + ((m + 1 : ℕ) : ℝ) • CFC.log M := by
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      abel
    calc
      _ = ∑ τ : Fin m → α, ∑ a : α,
          (NormedSpace.exp ((H + ∑ j, Y (τ j)) + Y a)).trace.re := hsplit
      _ ≤ ∑ τ : Fin m → α, (Fintype.card α : ℝ) *
          (NormedSpace.exp ((H + CFC.log M) + ∑ j, Y (τ j))).trace.re :=
        Finset.sum_le_sum fun τ _ ↦ hstep τ
      _ = (Fintype.card α : ℝ) *
          ∑ τ : Fin m → α, (NormedSpace.exp ((H + CFC.log M) + ∑ j, Y (τ j))).trace.re :=
        (Finset.mul_sum ..).symm
      _ ≤ (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) ^ m *
          (NormedSpace.exp ((H + CFC.log M) + (m : ℝ) • CFC.log M)).trace.re) :=
        mul_le_mul_of_nonneg_left (ih (hH.add IsSelfAdjoint.log.isHermitian))
          (Nat.cast_nonneg _)
      _ = _ := by rw [hfinal, pow_succ']; ring

end Matrix
