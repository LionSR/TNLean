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
* `mul_mul_exp_neg_le_of_log_le` — `K M e^{-x} ≤ ε` once `x ≥ log K + log M - log ε`, the last
  step from a logarithmic block-length threshold to the error `ε`.
* `mul_mul_exp_neg_div_le_of_le` — `K M e^{-q/a} ≤ ε` once `q ≥ a log(M q/ε) + a max(log K, 0)`.
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

/-- **From a logarithmic threshold to the error.** For `K, M, ε > 0`, if
`log K + log M - log ε ≤ x` then `K (M e^{-x}) ≤ ε`. This is the last step of the error bounds
of the log-depth preparation of arXiv:2307.01696 and of its paragraph "Connection to MERA",
where `x` is a multiple of the block length. -/
theorem mul_mul_exp_neg_le_of_log_le {K M ε x : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (h : Real.log K + Real.log M - Real.log ε ≤ x) : K * (M * Real.exp (-x)) ≤ ε := by
  calc K * (M * Real.exp (-x))
      = Real.exp (Real.log K + Real.log M - x) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log hK, Real.exp_log hM, Real.exp_neg]
        ring
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.2 (by linarith)
    _ = ε := Real.exp_log hε

/-- A divided logarithmic threshold gives the exponential error bound used to choose
one normalization cutoff before the ring length. -/
theorem mul_exp_neg_mul_le_of_div_log_le {K r ε x : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hε : 0 < ε)
    (h : (Real.log K - Real.log ε) / r ≤ x) : K * Real.exp (-(r * x)) ≤ ε := by
  have ht : Real.log K + Real.log 1 - Real.log ε ≤ r * x := by
    simpa only [Real.log_one, add_zero, mul_comm] using (div_le_iff₀ hr).mp h
  simpa only [one_mul] using mul_mul_exp_neg_le_of_log_le hK zero_lt_one hε ht

/-- **From a block-length threshold to the error.** For `K, a, ε > 0`, `M, q ≥ 1` and
`b ≥ a max(log K, 0)`, if `a log(M q/ε) + b ≤ q` then `K (M e^{-q/a}) ≤ ε`. This is the last
step of the error bounds of arXiv:2307.01696 for a block length `q` of `M` blocks with
`q ≥ a log(N/ε) + b`, `N = M q`. -/
theorem mul_mul_exp_neg_div_le_of_le {K M q a b ε : ℝ} (hK : 0 < K) (hM : 1 ≤ M) (hq : 1 ≤ q)
    (ha : 0 < a) (hε : 0 < ε) (hb : a * max (Real.log K) 0 ≤ b)
    (h : a * Real.log (M * q / ε) + b ≤ q) : K * (M * Real.exp (-(q / a))) ≤ ε := by
  have hM0 : 0 < M := by linarith
  have hq0 : 0 < q := by linarith
  refine mul_mul_exp_neg_le_of_log_le hK hM0 hε ?_
  rw [Real.log_div (mul_pos hM0 hq0).ne' hε.ne', Real.log_mul hM0.ne' hq0.ne'] at h
  rw [le_div_iff₀ ha]
  have hlogq : 0 ≤ a * Real.log q := mul_nonneg ha.le (Real.log_nonneg hq)
  have hKm : a * Real.log K ≤ a * max (Real.log K) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) ha.le
  nlinarith

/-- A polynomial-exponential error `K N^k exp(-r q)` is at most `ε` at every
`N ≥ 1`, `0 < ε ≤ 1`, once `q ≥ a log(N/ε) + b`, with
`a ≥ max(k,1)/r` and `b ≥ max(log K,0)/r`.

This scalar estimate makes the sufficient block coefficient explicit in the conditional
inhomogeneous preparation theorem associated with arXiv:2307.01696. In particular `k = 1`
requires `a ≥ 1/r`; this is a sufficient block coefficient, not an optimal circuit depth. -/
theorem mul_pow_mul_exp_neg_le_of_le {K r N ε a b q : ℝ} {k : ℕ}
    (hK : 0 < K) (hr : 0 < r) (hN : 1 ≤ N) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ha : max (k : ℝ) 1 / r ≤ a) (hb : max (Real.log K) 0 / r ≤ b)
    (hq : a * Real.log (N / ε) + b ≤ q) :
    K * (N ^ k * Real.exp (-(r * q))) ≤ ε := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  apply mul_mul_exp_neg_le_of_log_le hK (pow_pos hN0 k) hε
  rw [Real.log_pow]
  have hra : max (k : ℝ) 1 ≤ r * a := by
    simpa only [mul_comm] using (div_le_iff₀ hr).mp ha
  have hrb : Real.log K ≤ r * b :=
    (le_max_left _ _).trans (by simpa only [mul_comm] using (div_le_iff₀ hr).mp hb)
  have hlN := Real.log_nonneg hN
  have hlε := Real.log_nonpos hε.le hε1
  have hNmul := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hra) hlN
  have hεmul := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hra) (neg_nonneg.mpr hlε)
  have hrq := mul_le_mul_of_nonneg_left hq hr.le
  rw [Real.log_div hN0.ne' hε.ne'] at hrq
  nlinarith only [hrb, hNmul, hεmul, hrq]
