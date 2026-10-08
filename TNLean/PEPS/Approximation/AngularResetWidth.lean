/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-!
# Uniform reset-width estimates

The reset cost `C₃ * (1 + log s) ^ K + C₄ * log L` is eventually smaller than
`c * s`, uniformly over every real scale `s ≥ D * log L`. The slope `D` is fixed
before the system size `L` and scale `s`; one threshold works for all subsequent
sizes and scales. The proof uses logarithmic powers being sublinear, and allows
arbitrary real exponents and coefficients.

This is the scalar estimate following equation `eq:info-reset-scale-cost` in
*Polynomial PEPS approximation of gapped square-grid ground states*,
`02-information.tex`, lines 745–778, at source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. It does not establish the physical
reset statement or the angular information invariant.

Pinned source:
<https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex#L745-L778>.
All four declarations below have original Lean proofs; no upstream Lean proof
text was reused.
-/

open Filter
open scoped Topology

namespace TNLean.PEPS.Approximation

/-- Every fixed real logarithmic power has reset cost at most half of a positive
linear budget above one fixed scale. This supplies the sublinear estimate used
after equation `eq:info-reset-scale-cost`, without restricting `K` to integers.

Source: September 24, 2026, equation `eq:info-reset-scale-cost` and its ensuing argument.
Original Lean proof; no upstream Lean proof text reused. -/
theorem exists_reset_scale_polylog_le (K C₃ c : ℝ) (hc : 0 < c) :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ s : ℝ, S ≤ s →
      C₃ * (1 + Real.log s) ^ K ≤ (c / 2) * s := by
  have hsmall : (fun x : ℝ ↦ C₃ * Real.log x ^ K) =o[atTop] (fun x : ℝ ↦ x) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop K (show (0 : ℝ) < 1 by norm_num)).const_mul_left C₃
  have hbound := hsmall.bound (show 0 < c / (2 * Real.exp 1) by positivity)
  have hmul : Tendsto (fun s : ℝ ↦ Real.exp 1 * s) atTop atTop :=
    Tendsto.const_mul_atTop (Real.exp_pos 1) tendsto_id
  obtain ⟨S, hS⟩ := (hmul.eventually hbound).exists_forall_of_atTop
  refine ⟨max 1 S, le_max_left _ _, fun s hs ↦ ?_⟩
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 < s := zero_lt_one.trans_le hs1
  have hlog : Real.log (Real.exp 1 * s) = 1 + Real.log s := by
    rw [Real.log_mul (Real.exp_ne_zero 1) hs0.ne', Real.log_exp]
  calc
    C₃ * (1 + Real.log s) ^ K ≤ ‖C₃ * (1 + Real.log s) ^ K‖ :=
      Real.le_norm_self _
    _ ≤ (c / (2 * Real.exp 1)) * (Real.exp 1 * s) := by
      simpa only [hlog, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos 1).le hs0.le)]
        using hS s ((le_max_right _ _).trans hs)
    _ = (c / 2) * s := by field_simp

/-- Fixing a positive slope `D ≥ 4 * C₄ / c` gives a single size threshold for
every reset scale. The lower scale also exceeds `exp (max K 1)`, as required in
the argument following equation `eq:info-reset-scale-cost`. No coefficient or
threshold depends on the subsequently quantified size or scale.

Source: September 24, 2026, equation `eq:info-reset-scale-cost` and its ensuing argument.
Original Lean proof; no upstream Lean proof text reused. -/
theorem exists_angular_reset_width_bound_of_slope (K C₃ C₄ c D : ℝ)
    (hc : 0 < c) (hD : 0 < D) (hCD : 4 * C₄ / c ≤ D) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      Real.exp (max K 1) ≤ D * Real.log L ∧
      ∀ s : ℝ, D * Real.log L ≤ s →
        C₃ * (1 + Real.log s) ^ K + C₄ * Real.log L ≤ (3 * c / 4) * s ∧
          (3 * c / 4) * s < c * s := by
  obtain ⟨S, hS1, hS⟩ := exists_reset_scale_polylog_le K C₃ c hc
  let T := max S (Real.exp (max K 1))
  refine ⟨max 2 (Real.exp (T / D)), le_max_left _ _, fun L hL ↦ ?_⟩
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hexp : Real.exp (T / D) ≤ L := (le_max_right _ _).trans hL
  have hlog : T / D ≤ Real.log L := (Real.le_log_iff_exp_le hL0).2 hexp
  have hT : T ≤ D * Real.log L := by
    simpa only [mul_comm] using (div_le_iff₀ hD).1 hlog
  refine ⟨(le_max_right _ _).trans hT, fun s hs ↦ ?_⟩
  have hSs : S ≤ s := (le_max_left _ _).trans (hT.trans hs)
  have hs0 : 0 < s := (zero_lt_one.trans_le hS1).trans_le hSs
  have hpoly := hS s hSs
  have hCD' : 4 * C₄ ≤ D * c := (div_le_iff₀ hc).1 hCD
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlinear : C₄ * Real.log L ≤ (c / 4) * s := by
    have h₁ := mul_le_mul_of_nonneg_right hCD' hlog0
    have h₂ := mul_le_mul_of_nonneg_left hs hc.le
    nlinarith
  exact ⟨by linarith, by nlinarith [mul_pos hc hs0]⟩

/-- A fixed slope at least one and a fixed size threshold control all reset
scales. The proof chooses `D = max 1 (4 * C₄ / c)` before `L₀`, `L`, and `s`.
This proves the scalar uniformity step after `eq:info-reset-scale-cost`, including
zero coefficients and exponent zero.

Source: September 24, 2026, equation `eq:info-reset-scale-cost` and its ensuing argument.
Original Lean proof; no upstream Lean proof text reused. -/
theorem exists_angular_reset_width_bound (K C₃ C₄ c : ℝ) (hc : 0 < c) :
    ∃ D : ℝ, 1 ≤ D ∧ 4 * C₄ / c ≤ D ∧
      ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
        Real.exp (max K 1) ≤ D * Real.log L ∧
        ∀ s : ℝ, D * Real.log L ≤ s →
          C₃ * (1 + Real.log s) ^ K + C₄ * Real.log L ≤ (3 * c / 4) * s ∧
            (3 * c / 4) * s < c * s := by
  refine ⟨max 1 (4 * C₄ / c), le_max_left _ _, le_max_right _ _, ?_⟩
  exact exists_angular_reset_width_bound_of_slope K C₃ C₄ c _ hc
    (zero_lt_one.trans_le (le_max_left _ _)) (le_max_right _ _)

/-- Any width bounded by the reset-cost expression fits strictly inside the
available width, uniformly over all sizes and scales past one threshold.
The width assumption is equation `eq:info-reset-scale-cost`; the strict
conclusion is derived from the uniform scalar estimate.

Source: September 24, 2026, equation `eq:info-reset-scale-cost` and its ensuing argument.
Original Lean proof; no upstream Lean proof text reused. -/
theorem exists_angular_reset_width_lt_of_slope (K C₃ C₄ c D : ℝ)
    (hc : 0 < c) (hD : 0 < D) (hCD : 4 * C₄ / c ≤ D) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      ∀ s : ℝ, D * Real.log L ≤ s → ∀ w : ℝ,
        w ≤ C₃ * (1 + Real.log s) ^ K + C₄ * Real.log L → w < c * s := by
  obtain ⟨L₀, hL₀, hbound⟩ :=
    exists_angular_reset_width_bound_of_slope K C₃ C₄ c D hc hD hCD
  refine ⟨L₀, hL₀, fun L hL s hs w hw ↦ ?_⟩
  obtain ⟨hcost, hstrict⟩ := (hbound L hL).2 s hs
  exact (hw.trans hcost).trans_lt hstrict

end TNLean.PEPS.Approximation
