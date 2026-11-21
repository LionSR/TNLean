/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ExplicitThresholds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Qualitative error convergence does not give a uniform accuracy scale

The scalar errors `δ(N,q) = 1/(N+1)` for `q < N` and zero for `q ≥ N` decrease with blocking,
vanish for whole-ring blocking, and tend to zero along every blocking schedule. Nevertheless,
no single coefficient in `q ≤ C log(N/ε)` attains every accuracy uniformly in `N`.

This obstructs an inference from qualitative convergence alone in the inhomogeneous remark
of arXiv:2307.01696. It is an error-function counterexample, not a construction of MPS with
these optimal approximation errors or a circuit-depth lower bound. See
`docs/paper-gaps/mswc24_inhomogeneous_long_range.tex`.
-/

open Filter

namespace MPSPreparation

/-- An error decreasing with the blocking length and vanishing at whole-ring blocking. -/
noncomputable def delayedBlockingError (N q : ℕ) : ℝ :=
  if q < N then 1 / ((N : ℝ) + 1) else 0

/-- The delayed blocking error lies between zero and `1/(N+1)`. -/
theorem delayedBlockingError_bounds (N q : ℕ) :
    0 ≤ delayedBlockingError N q ∧ delayedBlockingError N q ≤ 1 / ((N : ℝ) + 1) := by
  unfold delayedBlockingError
  split_ifs <;> constructor <;> first | positivity | exact le_rfl

/-- Increasing the blocking length never increases the error. -/
theorem antitone_delayedBlockingError (N : ℕ) : Antitone (delayedBlockingError N) := by
  intro q q' hq
  unfold delayedBlockingError
  split_ifs <;> first | exact le_rfl | positivity | omega

/-- Whole-ring blocking has zero error. -/
theorem delayedBlockingError_eq_zero {N q : ℕ} (h : N ≤ q) :
    delayedBlockingError N q = 0 := ite_eq_right (by omega)

/-- Errors tend to zero along every schedule, hence in particular along any logarithmic one. -/
theorem tendsto_delayedBlockingError (q : ℕ → ℕ) :
    Tendsto (fun N => delayedBlockingError N (q N)) atTop (nhds 0) :=
  squeeze_zero (fun N => (delayedBlockingError_bounds N (q N)).1)
    (fun N => (delayedBlockingError_bounds N (q N)).2)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- At arbitrarily large ring lengths, accuracy `1/(2(N+1))` cannot be attained by any
blocking scale bounded by `C log(N/ε)`, for any proposed fixed nonnegative `C`. -/
theorem exists_delayedBlockingError_gt_of_log_bound (C : ℝ) (hC : 0 ≤ C) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ q : ℕ, (q : ℝ) ≤ C * Real.log ((N : ℝ) / ε) → ε < delayedBlockingError N q := by
  let N := max 2 (max N₀ ⌈Real.logPowThreshold (3 * C) (1 / 2) 1 1⌉₊)
  have hN2 : 2 ≤ N := le_max_left _ _
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hNth : ⌈Real.logPowThreshold (3 * C) (1 / 2) 1 1⌉₊ ≤ N + 1 := by
    have : ⌈Real.logPowThreshold (3 * C) (1 / 2) 1 1⌉₊ ≤ N :=
      (le_max_right _ _).trans (le_max_right _ _)
    omega
  have hsmall : 3 * C * Real.log ((N : ℝ) + 1) ≤ (1 / 2 : ℝ) * ((N : ℝ) + 1) := by
    simpa only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] using
      (Real.mul_log_pow_le_mul_rpow_of_ceil_logPowThreshold_le (n := N + 1)
        (mul_nonneg (by norm_num) hC) (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (0 : ℝ) < 1) hNth)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  let ε : ℝ := 1 / (2 * ((N : ℝ) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    rw [div_le_one (by positivity)]
    nlinarith
  have hlog : Real.log ((N : ℝ) / ε) ≤ 3 * Real.log ((N : ℝ) + 1) := by
    have heq : Real.log ((N : ℝ) / ε) =
        Real.log N + Real.log 2 + Real.log ((N : ℝ) + 1) := by
      dsimp [ε]
      rw [Real.log_div hNpos.ne' (by positivity),
        Real.log_div one_ne_zero (by positivity), Real.log_one,
        Real.log_mul (by norm_num) (by positivity)]
      ring
    rw [heq]
    have h₁ := Real.log_le_log hNpos (show (N : ℝ) ≤ N + 1 by linarith)
    have h₂ := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ N + 1 by linarith)
    linarith
  refine ⟨N, hN₀, hN2, ε, hε, hε1, fun q hq => ?_⟩
  have hqN : (q : ℝ) < N := by
    have := mul_le_mul_of_nonneg_left hlog hC
    nlinarith
  have hqN' : q < N := by exact_mod_cast hqN
  rw [delayedBlockingError, ite_eq_left hqN']
  dsimp [ε]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Qualitative convergence, monotonicity in the blocking length, and exact whole-ring
blocking do not imply a uniform logarithmic accuracy-dependent blocking coefficient. -/
theorem not_exists_uniform_log_blocking_for_delayedBlockingError :
    ¬∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ q : ℕ, (q : ℝ) ≤ C * Real.log ((N : ℝ) / ε) ∧ delayedBlockingError N q ≤ ε := by
  rintro ⟨C, hC, h⟩
  obtain ⟨N, _, hN, ε, hε, hε1, herr⟩ := exists_delayedBlockingError_gt_of_log_bound C hC 0
  obtain ⟨q, hq, hδ⟩ := h N hN ε hε hε1
  exact (not_lt_of_ge hδ) (herr q hq)

end MPSPreparation
