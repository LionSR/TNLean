/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.BellOverlapLogBound
import QICLean.Representation.ReplicaPrevector

/-!
# The lower remainder for the same physical label sequence

The supplied Schmidt--Bell sequence has logarithmic label dimension equal
to k times the selected-state entropy up to o(k). Its absolute discrepancy
therefore supplies the lower label defect, with no new label choice.
The complete explicit polynomial and label error in the actual sharp lower
estimate, divided by ak, tends to zero for each fixed physical instance.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 130--153,
255--281 and 585--651, revision adc7f124.
-/

noncomputable section

open Filter PermutationRepresentation
open scoped Topology

namespace TNLean.PEPS.AreaLaw.Scan

/-- The nonnegative lower-label defect of the same supplied sequence.
Source: `07-comparators.tex`, lines 255--281 and 585--651, adc7f124. -/
def sharpLowerLabelDefect
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) : ℝ :=
  2 * |Real.log (ell k).dim - (k : ℝ) * Sent|

/-- The same label on C and R obeys the lower entropy condition with its
actual absolute dimension discrepancy. No label is reselected.
Source: `07-comparators.tex`, lines 255--281 and 585--651, adc7f124. -/
theorem sharpLowerLabelDefect_label_bound
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) :
    0 ≤ sharpLowerLabelDefect ell Sent k ∧
      2 * (k : ℝ) * Sent - sharpLowerLabelDefect ell Sent k ≤
        Real.log (ell k).dim + Real.log (ell k).dim := by
  refine ⟨mul_nonneg (by norm_num) (abs_nonneg _), ?_⟩
  have h := le_abs_self ((k : ℝ) * Sent - Real.log (ell k).dim)
  rw [abs_sub_comm] at h
  dsimp only [sharpLowerLabelDefect]
  linarith only [h]

/-- The exact lower error after division by ak. The same label defect is
used in the finite-copy actual-root bound.
Source: `07-comparators.tex`, lines 585--651, adc7f124. -/
def sharpLowerRemainder (a c Cf : ℝ)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) : ℝ :=
  (2 * |Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
      a * sharpLowerLabelDefect ell Sent k| +
    |Real.log (((k : ℝ) + 2) ^ (-Cf) / 2)| + Real.log 2 + Real.log (3 / 2)) /
      (a * (k : ℝ))

/-- The exact little-o label conclusion of the physical prevector theorem
implies that its complete lower remainder vanishes. All physical dimensions,
the weight and the polynomial constants are fixed before the replica limit.
Source: `07-comparators.tex`, lines 255--281 and 585--651, adc7f124. -/
theorem tendsto_sharpLowerRemainder_of_label_dimension
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
      (fun k : ℕ => (k : ℝ))) (a c Cf : ℝ) :
    Tendsto (sharpLowerRemainder a c Cf ell Sent) atTop (𝓝 0) := by
  have hlog (b : ℝ) :
      Tendsto (fun k : ℕ => Real.log ((k : ℝ) + b) / (k : ℝ)) atTop (𝓝 0) := by
    have hshift : Tendsto (fun k : ℕ => (k : ℝ) + b) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-b) 1 one_ne_zero).comp hshift
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using hh
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hconst (b : ℝ) : Tendsto (fun k : ℕ => b / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul b
  have habs (f : ℕ → ℝ)
      (hf : Tendsto (fun k : ℕ => f k / (k : ℝ)) atTop (𝓝 0)) :
      Tendsto (fun k : ℕ => |f k| / (k : ℝ)) atTop (𝓝 0) := by
    have heq (k : ℕ) : |f k / (k : ℝ)| = |f k| / (k : ℝ) := by
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg k)]
    simpa only [heq, abs_zero] using hf.abs
  have hdefect : Tendsto
      (fun k : ℕ => sharpLowerLabelDefect ell Sent k / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [sharpLowerLabelDefect, mul_div_assoc, mul_zero] using
      (habs _ hdim.tendsto_div_nhds_zero).const_mul 2
  let r := fun k : ℕ => Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
    a * sharpLowerLabelDefect ell Sent k
  have hr : Tendsto (fun k : ℕ => r k / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [r, add_div, mul_div_assoc, mul_zero, add_zero] using
      ((hlog 1).add ((hlog 2).const_mul c)).add (hdefect.const_mul a)
  let b := fun k : ℕ => Real.log (((k : ℝ) + 2) ^ (-Cf) / 2)
  have hb_eq (k : ℕ) : b k = -Cf * Real.log ((k : ℝ) + 2) - Real.log 2 := by
    simp (disch := positivity) only [b, Real.log_div, Real.log_rpow]
  have hb : Tendsto (fun k : ℕ => b k / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [hb_eq, sub_div, mul_div_assoc, mul_zero, sub_zero] using
      ((hlog 2).const_mul (-Cf)).sub (hconst (Real.log 2))
  have herr : Tendsto (fun k : ℕ =>
      (2 * |r k| + |b k| + Real.log 2 + Real.log (3 / 2)) / (k : ℝ))
      atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
      ((((habs r hr).const_mul 2).add (habs b hb)).add
        (hconst (Real.log 2))).add (hconst (Real.log (3 / 2)))
  simpa only [sharpLowerRemainder, r, b, div_div, mul_comm, zero_div] using
    herr.div_const a

end TNLean.PEPS.AreaLaw.Scan
