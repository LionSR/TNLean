/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log

/-!
# Scalar choices for the output clause of the low-density algorithm

ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878, outputs states of energy at most
`E₀ + η - μ + δ`. The refinement of the low-density tree bounds the energy of its Ritz vectors
by `E₀ + ((1 + 1/ρ) x + (1 + ρ) A δ') / (1 - δ')` for every `ρ > 0`, where `x` is the top of the
shortened window, `A = ‖H - E₀‖` and `δ'` the accuracy of the refinement. This file chooses `ρ`
and `δ'` from the printed `δ`, so that the bound is at most `x + δ`, and compares the shortened
window with the printed `η - μ` for the source's buffer `w = μ / (3 log n)`.
-/

namespace TNLean.MPS.AreaLaw.ALVV

/-- For `x ≥ 0`, `A ≥ 0` and `δ > 0`, the choice `ρ = 3x/δ + 1` and
`δ' = min (1/2) (δ / (3 ((1 + ρ) A + x + δ + 1)))` gives `0 < δ' < 1` and
`((1 + 1/ρ) x + (1 + ρ) A δ') / (1 - δ') ≤ x + δ`. Auxiliary to ALVV, arXiv:1602.08828v2,
Theorem `t:alg2`, lines 1869–1878. -/
theorem low_density_output_accuracy {x A δ : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hδ : 0 < δ) :
    let ρ := 3 * x / δ + 1
    let d := min (1 / 2) (δ / (3 * ((1 + ρ) * A + x + δ + 1)))
    0 < ρ ∧ 0 < d ∧ d < 1 ∧ ((1 + 1 / ρ) * x + (1 + ρ) * A * d) / (1 - d) ≤ x + δ := by
  intro ρ d
  have hρ1 : 1 ≤ ρ := by
    have : 0 ≤ 3 * x / δ := by positivity
    dsimp only [ρ]; linarith
  have hρ : 0 < ρ := by linarith
  have hden : 0 < 3 * ((1 + ρ) * A + x + δ + 1) := by positivity
  have hd0 : 0 < d := lt_min (by norm_num) (by positivity)
  have hdhalf : d ≤ 1 / 2 := min_le_left _ _
  have hd1 : d < 1 := by linarith
  refine ⟨hρ, hd0, hd1, ?_⟩
  have hdle : d ≤ δ / (3 * ((1 + ρ) * A + x + δ + 1)) := min_le_right _ _
  have hdmul : d * (3 * ((1 + ρ) * A + x + δ + 1)) ≤ δ := by
    rwa [le_div_iff₀ hden] at hdle
  -- `x / ρ ≤ δ / 3`
  have hxρ : x / ρ ≤ δ / 3 := by
    have h3 : 3 * x / δ ≤ ρ := by dsimp only [ρ]; linarith
    have h3' : 3 * x ≤ ρ * δ := (div_le_iff₀ hδ).mp h3
    rw [div_le_iff₀ hρ]
    linarith
  have hp1 : 0 ≤ d * ((1 + ρ) * A + 1) := by positivity
  have hp2 : 0 ≤ d * (x + δ + 1) := by positivity
  have hA' : (1 + ρ) * A * d ≤ δ / 3 := by linarith
  have hxd : (x + δ) * d ≤ δ / 3 := by linarith
  rw [div_le_iff₀ (by linarith)]
  have h1 : (1 + 1 / ρ) * x = x + x / ρ := by ring
  rw [h1]
  nlinarith

/-- The source's buffer `w = μ / (3 log L)`, with the natural logarithm, shortens the window by
at least `μ` over `⌈log₂ L⌉ + 1` levels: `μ ≤ 3w (⌈log₂ L⌉ + 1)` for `L ≥ 2` and `μ ≥ 0`.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878. -/
theorem source_buffer_le_window_shortening {L : ℕ} (hL : 2 ≤ L) {μ : ℝ} (hμ : 0 ≤ μ) :
    μ ≤ 3 * (μ / (3 * Real.log L)) * ((Nat.clog 2 L : ℝ) + 1) := by
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hlog : 0 < Real.log L := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `log L ≤ clog₂ L · log 2 ≤ clog₂ L + 1`
  have hpow : (L : ℝ) ≤ 2 ^ Nat.clog 2 L := by exact_mod_cast Nat.le_pow_clog (by norm_num) L
  have hlogpow : Real.log L ≤ (Nat.clog 2 L : ℝ) * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hpow
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hc : 0 ≤ (Nat.clog 2 L : ℝ) := Nat.cast_nonneg _
  have hkey : Real.log L ≤ (Nat.clog 2 L : ℝ) + 1 := by nlinarith
  rw [show 3 * (μ / (3 * Real.log L)) = μ / Real.log L by field_simp]
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog]
  nlinarith

end TNLean.MPS.AreaLaw.ALVV
