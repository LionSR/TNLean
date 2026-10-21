/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import TNLean.Algebra.ExplicitThresholds

/-!
# Uniform reset-width estimates

The reset cost `C₃ * (1 + log s) ^ K + C₄ * log L` is eventually smaller than
`c * s`, uniformly over every real scale `s ≥ D * log L`. The slope `D` is fixed
before the system size `L` and scale `s`; one threshold works for all subsequent
sizes and scales. The proof uses logarithmic powers being sublinear, and allows
arbitrary real exponents and coefficients. Both thresholds are explicit:
`resetPolylogScale K C₃ c` bounds the polylogarithmic term through the closed-form
threshold `Real.logRpowThreshold`, and `angularResetWidthThreshold K C₃ c D` is the size
threshold `max(2, exp(max(S, e^{max(K,1)}) / D))` of the source argument.

This is the scalar estimate following equation `eq:info-reset-scale-cost` in
*Polynomial PEPS approximation of gapped square-grid ground states*,
`02-information.tex`, lines 745–778, at source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. It does not establish the physical
reset statement or the angular information invariant.

Pinned source:
<https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex#L745-L778>.
All declarations below have original Lean proofs; no upstream Lean proof
text was reused.
-/

namespace TNLean.PEPS.Approximation

/-- The explicit scale `S = L_* / e` above which `C₃ (1 + log s) ^ K ≤ (c / 2) s`, where
`L_* = logRpowThreshold (max C₃ 0) (c / (2 e)) 0 1 K` is the threshold beyond which
`max(C₃, 0) (log x) ^ K ≤ (c / (2 e)) x`; the substitution `x = e s` turns `log x` into
`1 + log s`. This replaces the limit `(log x) ^ K / x → 0` used after equation
`eq:info-reset-scale-cost` by a closed-form scale.

Source: September 24, 2026, `02-information.tex`, lines 761–768. -/
noncomputable def resetPolylogScale (K C₃ c : ℝ) : ℝ :=
  Real.logRpowThreshold (max C₃ 0) (c / (2 * Real.exp 1)) 0 1 K / Real.exp 1

/-- The polylogarithmic reset scale is at least one. -/
theorem one_le_resetPolylogScale (K C₃ c : ℝ) : 1 ≤ resetPolylogScale K C₃ c := by
  unfold resetPolylogScale
  rw [one_le_div (Real.exp_pos 1)]
  exact le_max_left _ _

/-- **Sublinear polylogarithmic width, with an explicit scale.** For every real exponent `K`
and coefficient `C₃` and every `c > 0`, `C₃ (1 + log s) ^ K ≤ (c / 2) s` for every
`s ≥ resetPolylogScale K C₃ c`.

Source: September 24, 2026, equation `eq:info-reset-scale-cost` and the threshold choice at
`02-information.tex`, lines 761–768. -/
theorem reset_scale_polylog_le_of_resetPolylogScale_le {K C₃ c s : ℝ} (hc : 0 < c)
    (hs : resetPolylogScale K C₃ c ≤ s) :
    C₃ * (1 + Real.log s) ^ K ≤ (c / 2) * s := by
  have hs1 : 1 ≤ s := (one_le_resetPolylogScale K C₃ c).trans hs
  have hs0 : 0 < s := zero_lt_one.trans_le hs1
  have hx : Real.logRpowThreshold (max C₃ 0) (c / (2 * Real.exp 1)) 0 1 K ≤
      Real.exp 1 * s := by
    rw [mul_comm (Real.exp 1) s]
    exact (div_le_iff₀ (Real.exp_pos 1)).1 hs
  have hmain := Real.mul_rpow_mul_log_rpow_le_mul_rpow_of_logRpowThreshold_le
    (le_max_right C₃ 0) (by positivity : 0 < c / (2 * Real.exp 1)) zero_lt_one hx
  have hlog : Real.log (Real.exp 1 * s) = 1 + Real.log s := by
    rw [Real.log_mul (Real.exp_ne_zero 1) hs0.ne', Real.log_exp]
  rw [Real.rpow_zero, mul_one, Real.rpow_one, hlog] at hmain
  have hbase : 0 ≤ (1 + Real.log s) ^ K :=
    Real.rpow_nonneg (by linarith [Real.log_nonneg hs1]) _
  calc
    C₃ * (1 + Real.log s) ^ K ≤ max C₃ 0 * (1 + Real.log s) ^ K :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hbase
    _ ≤ c / (2 * Real.exp 1) * (Real.exp 1 * s) := hmain
    _ = (c / 2) * s := by field_simp

/-- Every fixed real logarithmic power has reset cost at most half of a positive
linear budget above one fixed scale. This supplies the sublinear estimate used
after equation `eq:info-reset-scale-cost`, without restricting `K` to integers.
The scale is `resetPolylogScale K C₃ c`
(`reset_scale_polylog_le_of_resetPolylogScale_le`).

Source: September 24, 2026, equation `eq:info-reset-scale-cost` and its ensuing argument.
Original Lean proof; no upstream Lean proof text reused. -/
theorem exists_reset_scale_polylog_le (K C₃ c : ℝ) (hc : 0 < c) :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ s : ℝ, S ≤ s →
      C₃ * (1 + Real.log s) ^ K ≤ (c / 2) * s :=
  ⟨resetPolylogScale K C₃ c, one_le_resetPolylogScale K C₃ c,
    fun _ hs ↦ reset_scale_polylog_le_of_resetPolylogScale_le hc hs⟩

/-- The size threshold `L₀ = max(2, exp(T / D))` with `T = max(S, e^{max(K,1)})` and
`S = resetPolylogScale K C₃ c`. For `L ≥ L₀` the lower scale `D log L` exceeds both `S` and
`e^{max(K,1)}`, as required after equation `eq:info-reset-scale-cost`.

Source: September 24, 2026, `02-information.tex`, lines 761–768. -/
noncomputable def angularResetWidthThreshold (K C₃ c D : ℝ) : ℝ :=
  max 2 (Real.exp (max (resetPolylogScale K C₃ c) (Real.exp (max K 1)) / D))

/-- The angular reset-width threshold is at least two. -/
theorem two_le_angularResetWidthThreshold (K C₃ c D : ℝ) :
    2 ≤ angularResetWidthThreshold K C₃ c D :=
  le_max_left _ _

/-- The angular reset-width threshold does not increase with the slope `D > 0`. -/
theorem angularResetWidthThreshold_anti {K C₃ c D D' : ℝ} (hD : 0 < D) (hDD' : D ≤ D') :
    angularResetWidthThreshold K C₃ c D' ≤ angularResetWidthThreshold K C₃ c D := by
  have hT : 0 ≤ max (resetPolylogScale K C₃ c) (Real.exp (max K 1)) :=
    (Real.exp_pos _).le.trans (le_max_right _ _)
  exact max_le_max le_rfl (Real.exp_le_exp.2 (div_le_div_of_nonneg_left hT hD hDD'))

/-- **Uniform width at every scale, with an explicit threshold.** Fix a positive slope
`D ≥ 4 * C₄ / c`. For every `L ≥ angularResetWidthThreshold K C₃ c D` the lower scale
`D log L` exceeds `exp (max K 1)`, and every `s ≥ D log L` has reset cost at most `3 c s / 4`.

Source: September 24, 2026, equation `eq:info-reset-scale-cost` and its ensuing argument,
`02-information.tex`, lines 744–774. -/
theorem angular_reset_width_bound_of_threshold_le {K C₃ C₄ c D : ℝ}
    (hc : 0 < c) (hD : 0 < D) (hCD : 4 * C₄ / c ≤ D) {L : ℝ}
    (hL : angularResetWidthThreshold K C₃ c D ≤ L) :
    Real.exp (max K 1) ≤ D * Real.log L ∧
      ∀ s : ℝ, D * Real.log L ≤ s →
        C₃ * (1 + Real.log s) ^ K + C₄ * Real.log L ≤ (3 * c / 4) * s ∧
          (3 * c / 4) * s < c * s := by
  let T := max (resetPolylogScale K C₃ c) (Real.exp (max K 1))
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hexp : Real.exp (T / D) ≤ L := (le_max_right _ _).trans hL
  have hlog : T / D ≤ Real.log L := (Real.le_log_iff_exp_le hL0).2 hexp
  have hT : T ≤ D * Real.log L := by
    simpa only [mul_comm] using (div_le_iff₀ hD).1 hlog
  refine ⟨(le_max_right _ _).trans hT, fun s hs ↦ ?_⟩
  have hSs : resetPolylogScale K C₃ c ≤ s := (le_max_left _ _).trans (hT.trans hs)
  have hs0 : 0 < s := (zero_lt_one.trans_le (one_le_resetPolylogScale K C₃ c)).trans_le hSs
  have hpoly := reset_scale_polylog_le_of_resetPolylogScale_le hc hSs
  have hCD' : 4 * C₄ ≤ D * c := (div_le_iff₀ hc).1 hCD
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlinear : C₄ * Real.log L ≤ (c / 4) * s := by
    have h₁ := mul_le_mul_of_nonneg_right hCD' hlog0
    have h₂ := mul_le_mul_of_nonneg_left hs hc.le
    nlinarith
  exact ⟨by linarith, by nlinarith [mul_pos hc hs0]⟩

/-- Fixing a positive slope `D ≥ 4 * C₄ / c` gives a single size threshold for
every reset scale. The lower scale also exceeds `exp (max K 1)`, as required in
the argument following equation `eq:info-reset-scale-cost`. No coefficient or
threshold depends on the subsequently quantified size or scale. The threshold is
`angularResetWidthThreshold K C₃ c D` (`angular_reset_width_bound_of_threshold_le`).

Source: September 24, 2026, equation `eq:info-reset-scale-cost` and its ensuing argument.
Original Lean proof; no upstream Lean proof text reused. -/
theorem exists_angular_reset_width_bound_of_slope (K C₃ C₄ c D : ℝ)
    (hc : 0 < c) (hD : 0 < D) (hCD : 4 * C₄ / c ≤ D) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      Real.exp (max K 1) ≤ D * Real.log L ∧
      ∀ s : ℝ, D * Real.log L ≤ s →
        C₃ * (1 + Real.log s) ^ K + C₄ * Real.log L ≤ (3 * c / 4) * s ∧
          (3 * c / 4) * s < c * s :=
  ⟨angularResetWidthThreshold K C₃ c D, two_le_angularResetWidthThreshold K C₃ c D,
    fun _ hL ↦ angular_reset_width_bound_of_threshold_le hc hD hCD hL⟩

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

/-- **Fitting an upper-bounded reset width, with an explicit threshold.** For a positive
slope `D ≥ 4 * C₄ / c`, every `L ≥ angularResetWidthThreshold K C₃ c D` and every
`s ≥ D log L`, any width bounded by the reset cost `C₃ (1 + log s) ^ K + C₄ log L` is
strictly smaller than `c s`.

Source: September 24, 2026, equation `eq:info-reset-scale-cost` and its ensuing argument,
`02-information.tex`, lines 744–774. -/
theorem angular_reset_width_lt_of_threshold_le {K C₃ C₄ c D : ℝ}
    (hc : 0 < c) (hD : 0 < D) (hCD : 4 * C₄ / c ≤ D) {L : ℝ}
    (hL : angularResetWidthThreshold K C₃ c D ≤ L) :
    ∀ s : ℝ, D * Real.log L ≤ s → ∀ w : ℝ,
      w ≤ C₃ * (1 + Real.log s) ^ K + C₄ * Real.log L → w < c * s := by
  intro s hs w hw
  obtain ⟨hcost, hstrict⟩ := (angular_reset_width_bound_of_threshold_le hc hD hCD hL).2 s hs
  exact (hw.trans hcost).trans_lt hstrict

/-- Any width bounded by the reset-cost expression fits strictly inside the
available width, uniformly over all sizes and scales past one threshold.
The width assumption is equation `eq:info-reset-scale-cost`; the strict
conclusion is derived from the uniform scalar estimate. The threshold is
`angularResetWidthThreshold K C₃ c D` (`angular_reset_width_lt_of_threshold_le`).

Source: September 24, 2026, equation `eq:info-reset-scale-cost` and its ensuing argument.
Original Lean proof; no upstream Lean proof text reused. -/
theorem exists_angular_reset_width_lt_of_slope (K C₃ C₄ c D : ℝ)
    (hc : 0 < c) (hD : 0 < D) (hCD : 4 * C₄ / c ≤ D) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      ∀ s : ℝ, D * Real.log L ≤ s → ∀ w : ℝ,
        w ≤ C₃ * (1 + Real.log s) ^ K + C₄ * Real.log L → w < c * s :=
  ⟨angularResetWidthThreshold K C₃ c D, two_le_angularResetWidthThreshold K C₃ c D,
    fun _ hL ↦ angular_reset_width_lt_of_threshold_le hc hD hCD hL⟩

end TNLean.PEPS.Approximation
