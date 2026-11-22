/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial decay of the Schmidt tail after Hastings

Write `τ k` for the mass of the squared Schmidt coefficients of a ground state beyond the
`k` largest ones. Hastings' eq. `constraint`, with `P = 1/2`, bounds `τ k` by
`c e^{-2m/ξ'}` as soon as `k ≥ k₀ D^{2m}`. This file turns that geometric family of
bounds into one polynomial bound in `k / k₀`, eq. `est`.

Source: Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4,
section "Matrix Product States", lines 540–552, eqs. `constraint` and `est`.

**Local fix (constant in eq. `est`):** the source bounds the tail by
`c exp(-⌊log_D(k'/k₀)⌋/ξ') ≤ c e^{1/ξ'} (k'/k₀)^{1/(ξ' ln D)}`. Eq. `constraint` holds
only at the even exponents `2m`, so an odd `⌊log_D(k'/k₀)⌋` loses one further factor
`e^{1/ξ'}`. The bound proved here therefore has constant `c e^{2/ξ'}`. The printed exponent
also lacks its minus sign. Documented in
`docs/paper-gaps/hastings07_schmidt_tail_constant.tex`.

## Main statements

* `TNLean.MPS.AreaLaw.Hastings.schmidtTail_le_rpow_of_geometric`: the stage lemma from
  eq. `constraint` to eq. `est`. It takes eq. `constraint` as a hypothesis; the bootstrap
  lemma supplies it.
-/

open Real

namespace TNLean.MPS.AreaLaw.Hastings

/-- **Stage lemma: from eq. `constraint` to eq. `est`.** Let `D > 1`, `ξ > 0`, `c ≥ 0` and
`k₀ > 0`. If a tail function `τ` satisfies `τ k ≤ c e^{-2m/ξ}` whenever `k₀ D^{2m} ≤ k`,
then for every `k ≥ k₀`,
`τ k ≤ c e^{2/ξ} (k/k₀)^{-1/(ξ log D)}`.
Hastings, arXiv:0705.2024v4, lines 540–552. The constant is `e^{2/ξ}` rather than the
printed `e^{1/ξ}`, and the exponent carries its minus sign; see the module docstring. -/
theorem schmidtTail_le_rpow_of_geometric {D ξ c k₀ : ℝ} (hD : 1 < D) (hξ : 0 < ξ)
    (hc : 0 ≤ c) (hk₀ : 0 < k₀) (τ : ℕ → ℝ)
    (hτ : ∀ m k : ℕ, k₀ * D ^ (2 * m) ≤ k → τ k ≤ c * exp (-(2 * m) / ξ))
    {k : ℕ} (hk : k₀ ≤ k) :
    τ k ≤ c * exp (2 / ξ) * ((k : ℝ) / k₀) ^ (-1 / (ξ * log D)) := by
  have hlogD : 0 < log D := log_pos hD
  have hD0 : 0 < D := by linarith
  have hr : 1 ≤ (k : ℝ) / k₀ := (one_le_div hk₀).mpr hk
  have hr0 : 0 < (k : ℝ) / k₀ := by linarith
  -- `x = log_D (k / k₀)` and `n = ⌊x⌋`; eq. `constraint` is used at `m = ⌊n / 2⌋`.
  set x : ℝ := log ((k : ℝ) / k₀) / log D with hx
  have hx0 : 0 ≤ x := div_nonneg (log_nonneg hr) hlogD.le
  set n : ℕ := ⌊x⌋₊ with hn
  set m : ℕ := n / 2 with hm
  have hDx : D ^ x = (k : ℝ) / k₀ := by
    rw [hx, rpow_def_of_pos hD0, mul_div_cancel₀ _ hlogD.ne', exp_log hr0]
  have hpow : k₀ * D ^ (2 * m) ≤ k := by
    have h2m : ((2 * m : ℕ) : ℝ) ≤ x :=
      le_trans (by exact_mod_cast (Nat.mul_div_le n 2)) (Nat.floor_le hx0)
    have : D ^ (2 * m) ≤ (k : ℝ) / k₀ := by
      rw [← hDx, ← rpow_natCast]
      exact rpow_le_rpow_of_exponent_le hD.le h2m
    rwa [le_div_iff₀ hk₀, mul_comm] at this
  have hstep := hτ m k hpow
  -- `2m ≥ n - 1 > x - 2`.
  have hmx : x - 2 ≤ 2 * (m : ℝ) := by
    have h1 : (n : ℝ) ≤ 2 * m + 1 := by
      have : n ≤ 2 * m + 1 := by omega
      exact_mod_cast this
    have h2 : x < n + 1 := Nat.lt_floor_add_one x
    linarith
  have hrpow : ((k : ℝ) / k₀) ^ (-1 / (ξ * log D)) = exp (-x / ξ) := by
    rw [rpow_def_of_pos hr0, hx]
    congr 1
    field_simp
  calc τ k ≤ c * exp (-(2 * m) / ξ) := hstep
    _ ≤ c * exp (-(x - 2) / ξ) := by
        gcongr
    _ = c * exp (2 / ξ) * ((k : ℝ) / k₀) ^ (-1 / (ξ * log D)) := by
        rw [hrpow, mul_assoc, ← exp_add]
        congr 2
        ring

end TNLean.MPS.AreaLaw.Hastings
