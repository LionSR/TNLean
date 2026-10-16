/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Scalar elimination of the actual selected entropy losses

This module is the arithmetic interface between the actual same-point sharp
comparison and its physical information bound. The caller must derive the
entropy estimates and the actual comparison. The final lemma takes only the
replica limit at fixed physical data, weight and positive smoothing parameter.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 868--911, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Filter
open scoped Topology

namespace TNLean.PEPS.AreaLaw.Scan

/-- The explicit scalar expression after eliminating the selected dimension,
selected entropy, actual pre-average and actual finite pre-maximum. Here `S`
is the same physical target entropy and `c = w - log z`. -/
def sharpInformationBound (S c Bpre logz W τ δ fixed continuity : ℝ) : ℝ :=
  (4 * S + 4 * c - 2 * logz) / W +
    (τ + δ / τ) * (2 * (S + c) + Bpre) + fixed + 2 * c + continuity

/-- Substitute upper bounds into the literal sharp comparison and its
actual information bridge. No choice of state, tree, point or parameter is
made by this scalar implication. -/
theorem two_information_le_sharpInformationBound
    {information S Sent logd Gpre Gpost gmax c Bpre logz W τ δ fixed
      continuity remainder : ℝ}
    (hW : 0 < W) (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (hS : 0 ≤ S) (hc : 0 ≤ c) (hBpre : 0 ≤ Bpre)
    (hlogd : logd ≤ S + c) (hSent : Sent ≤ S + c)
    (hGpre : Gpre ≤ Bpre) (hgmax : gmax ≤ Bpre)
    (hsharp : 2 * Sent + Gpre - Gpost ≤
      2 * (2 * logd - logz) / W + τ * Gpre + 2 * τ * logd + fixed +
        δ / τ * max 0 (2 * Sent + gmax) + remainder)
    (hinformation : 2 * information ≤ 2 * Sent + Gpre - Gpost +
      2 * c + continuity) :
    2 * information ≤
      sharpInformationBound S c Bpre logz W τ δ fixed continuity + remainder := by
  have hfirst : 2 * (2 * logd - logz) / W ≤
      (4 * S + 4 * c - 2 * logz) / W :=
    div_le_div_of_nonneg_right (by linarith only [hlogd]) hW.le
  have hpre := mul_le_mul_of_nonneg_left hGpre hτ.le
  have hdim := mul_le_mul_of_nonneg_left hlogd (by positivity : 0 ≤ 2 * τ)
  have hmax : max 0 (2 * Sent + gmax) ≤ 2 * (S + c) + Bpre :=
    max_le (by positivity) (by linarith only [hSent, hgmax])
  have hdefect := mul_le_mul_of_nonneg_left hmax (div_nonneg hδ hτ.le)
  unfold sharpInformationBound
  nlinarith only [hsharp, hinformation, hfirst, hpre, hdim, hdefect]

/-- Remove the three actual replica remainders at fixed physical data,
weight and smoothing parameter. The selected point may vary with `k`: the
scalar right side no longer contains it. No size limit is taken here. -/
theorem information_le_of_eventually_sharpInformationBound
    {information S c Bpre logz W τ δ fixed continuity g : ℝ}
    {rem upper lower : ℕ → ℝ}
    (hrem : Tendsto rem atTop (𝓝 0))
    (hupper : Tendsto upper atTop (𝓝 0))
    (hlower : Tendsto lower atTop (𝓝 0))
    (hbound : ∀ᶠ k : ℕ in atTop,
      2 * information ≤
        sharpInformationBound S c Bpre logz W τ
          (δ + rem k / (g / 2)) fixed continuity +
            (2 * upper k / W + lower k)) :
    2 * information ≤
      sharpInformationBound S c Bpre logz W τ δ fixed continuity := by
  have hdelta : Tendsto (fun k ↦ δ + rem k / (g / 2)) atTop (𝓝 δ) := by
    simpa only [zero_div, add_zero] using
      tendsto_const_nhds.add (hrem.div_const (g / 2))
  have hmain : Tendsto
      (fun k ↦ sharpInformationBound S c Bpre logz W τ
        (δ + rem k / (g / 2)) fixed continuity) atTop
      (𝓝 (sharpInformationBound S c Bpre logz W τ δ fixed continuity)) := by
    unfold sharpInformationBound
    exact ((((tendsto_const_nhds.add
      ((tendsto_const_nhds.add (hdelta.div_const τ)).mul_const
        (2 * (S + c) + Bpre))).add_const fixed).add_const (2 * c)).add_const continuity)
  have hrest : Tendsto (fun k ↦ 2 * upper k / W + lower k) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div, zero_add] using
      ((hupper.const_mul 2).div_const W).add hlower
  have hlimit := hmain.add hrest
  simp only [add_zero] at hlimit
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlimit hbound

end TNLean.PEPS.AreaLaw.Scan
