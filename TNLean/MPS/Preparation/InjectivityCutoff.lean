/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Below the cutoff every injectivity length is reached

The proofs of the approximation error of arXiv:2307.01696 (Supplemental Material, Lemma 1' and
eq. (S12)) bound `ε ≤ C u e^{C u}` with `u = M x^q`, `x = e^{-γ/ξ}`. When `C u ≥ 1` the bound is
trivial since `ε ≤ 1`. When `C u < 1` and `C` dominates `1 + ∑ⱼ x^{-L_j}` for the injectivity
lengths `L_j` of the blocks, the base satisfies `x < 1` and every block length `q` is at least
every `L_j`, so every `q`-site blocked tensor is injective. This file isolates that step.

## Main declarations

* `Real.exp_neg_mul_div_eq_pow` — `e^{-γ q/ξ} = (e^{-γ/ξ})^q`.
* `lt_one_and_forall_le_of_mul_mul_pow_lt_one` — `C (M x^q) < 1` forces `x < 1` and `L_j ≤ q`.
* `le_mul_mul_exp_of_forall_le` — the bound `ε ≤ C u e^{C u}` follows from `ε ≤ 1` and from the
  bound in the case `x < 1`, `L_j ≤ q` for every `j`.
-/

open scoped BigOperators

/-- The rate `e^{-γ q/ξ}` of arXiv:2307.01696 is the `q`-th power of `e^{-γ/ξ}`. -/
theorem Real.exp_neg_mul_div_eq_pow (γ ξ : ℝ) (q : ℕ) :
    Real.exp (-γ * q / ξ) = Real.exp (-γ / ξ) ^ q := by
  rw [← Real.exp_nat_mul]; congr 1; ring

/-- If `C ≥ 1 + ∑ⱼ x^{-L_j}` with `x > 0`, `M ≥ 1`, and `C (M x^q) < 1`, then `x < 1` and
`L_j ≤ q` for every `j`. This is the step of the proof of arXiv:2307.01696, Supplemental
Material, Lemma 1', which reduces the error bound for block lengths below the injectivity lengths
`L_j` to the trivial bound `ε ≤ 1`. -/
theorem lt_one_and_forall_le_of_mul_mul_pow_lt_one {ι : Type*} [Fintype ι] {x C M : ℝ}
    (hx : 0 < x) {L : ι → ℕ} (hC : 1 + ∑ j, (x ^ L j)⁻¹ ≤ C) (hM : 1 ≤ M) {q : ℕ}
    (h : C * (M * x ^ q) < 1) : x < 1 ∧ ∀ j, L j ≤ q := by
  have hS : 0 ≤ ∑ j, (x ^ L j)⁻¹ := Finset.sum_nonneg fun j _ => by positivity
  have hu : 0 ≤ M * x ^ q := by positivity
  have hx1 : x < 1 := by
    by_contra hx1
    rw [not_lt] at hx1
    have : 1 ≤ M * x ^ q := one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ hx1)
    nlinarith
  refine ⟨hx1, fun j => ?_⟩
  by_contra hj
  rw [not_le] at hj
  have h1 : x ^ L j ≤ M * x ^ q :=
    (pow_le_pow_of_le_one hx.le hx1.le hj.le).trans (le_mul_of_one_le_left (by positivity) hM)
  have h2 : 1 ≤ (x ^ L j)⁻¹ * (M * x ^ q) := by
    rw [← inv_mul_cancel₀ (by positivity : x ^ L j ≠ 0)]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : (x ^ L j)⁻¹ ≤ ∑ j, (x ^ L j)⁻¹ :=
    Finset.single_le_sum (f := fun j => (x ^ L j)⁻¹) (fun j _ => by positivity)
      (Finset.mem_univ j)
  have h4 : (x ^ L j)⁻¹ * (M * x ^ q) ≤ C * (M * x ^ q) :=
    mul_le_mul_of_nonneg_right (by linarith) hu
  linarith

/-- **The trivial range of the error bound.** Let `C ≥ 1 + ∑ⱼ x^{-L_j}` with `x > 0`, `M ≥ 1`,
and `ε ≤ 1`. To prove `ε ≤ C u e^{C u}` with `u = M x^q` it suffices to prove it when `x < 1`,
`L_j ≤ q` for every `j`, and `C u < 1`: otherwise `C u ≥ 1` and the bound follows from `ε ≤ 1`.
This is the reduction to injective blocked tensors in the proof of arXiv:2307.01696,
Supplemental Material, Lemma 1'. -/
theorem le_mul_mul_exp_of_forall_le {ι : Type*} [Fintype ι] {x C M ε : ℝ} (hx : 0 < x)
    {L : ι → ℕ} (hC : 1 + ∑ j, (x ^ L j)⁻¹ ≤ C) (hM : 1 ≤ M) {q : ℕ} (hε : ε ≤ 1)
    (h : x < 1 → (∀ j, L j ≤ q) → C * (M * x ^ q) < 1 →
      ε ≤ C * (M * x ^ q) * Real.exp (C * (M * x ^ q))) :
    ε ≤ C * (M * x ^ q) * Real.exp (C * (M * x ^ q)) := by
  have hS : 0 ≤ ∑ j, (x ^ L j)⁻¹ := Finset.sum_nonneg fun j _ => by positivity
  have hC0 : 0 ≤ C := by linarith
  have hu : 0 ≤ M * x ^ q := by positivity
  by_cases hbig : 1 ≤ C * (M * x ^ q)
  · exact hε.trans (hbig.trans (le_mul_of_one_le_right (by positivity)
      (Real.one_le_exp (by positivity))))
  rw [not_le] at hbig
  obtain ⟨hx1, hLq⟩ := lt_one_and_forall_le_of_mul_mul_pow_lt_one hx hC hM hbig
  exact h hx1 hLq hbig
