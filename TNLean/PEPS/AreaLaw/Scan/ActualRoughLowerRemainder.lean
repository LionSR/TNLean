/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.BellOverlapLogBound
import QICLean.Representation.ReplicaPrevector

/-!
# The rough lower remainder for the same physical label sequence

The supplied auxiliary label sequence is unchanged. Its logarithmic dimension
error is o(k), so the complete coefficient-three rough remainder tends to zero.
The band count, all dimensions and polynomial constants are fixed in this limit.
The replica threshold is independent of the actual fill/charge round and its
interpolation parameter.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 130--169,
255--281 and 585--651; `08-scanner.tex`, lines 755--769, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Filter PermutationRepresentation
open scoped Topology

namespace TNLean.PEPS.AreaLaw.Scan

/-- The nonnegative lower-label defect of the same supplied sequence.
Source: `07-comparators.tex`, lines 255--281 and 585--651, adc7f124. -/
def roughLowerLabelDefect
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) : ℝ :=
  2 * |Real.log (ell k).dim - (k : ℝ) * Sent|

/-- The same label on C and R obeys the lower entropy condition with its
actual absolute dimension discrepancy. No label is reselected.
Source: `07-comparators.tex`, lines 255--281 and 585--651, adc7f124. -/
theorem roughLowerLabelDefect_label_bound
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) :
    0 ≤ roughLowerLabelDefect ell Sent k ∧
      2 * (k : ℝ) * Sent - roughLowerLabelDefect ell Sent k ≤
        Real.log (ell k).dim + Real.log (ell k).dim := by
  refine ⟨mul_nonneg (by norm_num) (abs_nonneg _), ?_⟩
  have h := le_abs_self ((k : ℝ) * Sent - Real.log (ell k).dim)
  rw [abs_sub_comm] at h
  dsimp only [roughLowerLabelDefect]
  linarith only [h]

/-- The replica remainder at an arbitrary fixed per-band weight.
Source: area-law manuscript, 07-comparators.tex, lines 97--169 and 585--651. -/
def roughLowerRemainderAtWeight (Kband : ℕ) (a c Cf : ℝ)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) : ℝ :=
  ((Kband : ℝ) / 2 *
    (2 * |Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
      a * roughLowerLabelDefect ell Sent k| +
      Cf * Real.log ((k : ℝ) + 2) + 2 * Real.log 2 + Real.log (3 / 2))) /
        (k : ℝ)

/-- The same supplied label sequence makes the fixed-weight remainder vanish.
Source: area-law manuscript, 07-comparators.tex, lines 255--281 and 585--651. -/
theorem tendsto_roughLowerRemainderAtWeight_of_label_dimension
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
      (fun k : ℕ => (k : ℝ))) (Kband : ℕ) (a c Cf : ℝ) :
    Tendsto (roughLowerRemainderAtWeight Kband a c Cf ell Sent) atTop (𝓝 0) := by
  have hlog (b : ℝ) :
      Tendsto (fun k : ℕ => Real.log ((k : ℝ) + b) / (k : ℝ)) atTop (𝓝 0) := by
    have hshift : Tendsto (fun k : ℕ => (k : ℝ) + b) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-b) 1 one_ne_zero).comp hshift
    simpa only [Function.comp_def, pow_one, _root_.one_mul, add_neg_cancel_right] using hh
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hconst (b : ℝ) : Tendsto (fun k : ℕ => b / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul b
  have habs (f : ℕ → ℝ)
      (hf : Tendsto (fun k : ℕ => f k / (k : ℝ)) atTop (𝓝 0)) :
      Tendsto (fun k : ℕ => |f k| / (k : ℝ)) atTop (𝓝 0) := by
    have heq (k : ℕ) : |f k / (k : ℝ)| = |f k| / (k : ℝ) := by
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    simpa only [heq, abs_zero] using hf.abs
  have hdefect : Tendsto
      (fun k : ℕ => roughLowerLabelDefect ell Sent k / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [roughLowerLabelDefect, mul_div_assoc, mul_zero] using
      (habs _ hdim.tendsto_div_nhds_zero).const_mul 2
  let r := fun k : ℕ => Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
    a * roughLowerLabelDefect ell Sent k
  have hr : Tendsto (fun k : ℕ => r k / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [r, add_div, mul_div_assoc, mul_zero, add_zero] using
      ((hlog 1).add ((hlog 2).const_mul c)).add (hdefect.const_mul a)
  have herr : Tendsto (fun k : ℕ =>
      (2 * |r k| + Cf * Real.log ((k : ℝ) + 2) +
        2 * Real.log 2 + Real.log (3 / 2)) / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
      ((((habs r hr).const_mul 2).add ((hlog 2).const_mul Cf)).add
        (hconst (2 * Real.log 2))).add (hconst (Real.log (3 / 2)))
  change Tendsto (fun k : ℕ =>
      ((Kband : ℝ) / 2 * (2 * |r k| + Cf * Real.log ((k : ℝ) + 2) +
        2 * Real.log 2 + Real.log (3 / 2))) / (k : ℝ)) atTop (𝓝 0)
  simpa only [mul_div_assoc, mul_zero] using
    herr.const_mul ((Kband : ℝ) / 2)


/-- The exact remainder of the coefficient-three rough estimate, with the
same supplied label sequence and total band weight four.
Source: `07-comparators.tex`, lines 585--651; `08-scanner.tex`, 755--769. -/
def roughLowerRemainder (Kband : ℕ) (c Cf : ℝ)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) : ℝ :=
  roughLowerRemainderAtWeight Kband (4 / (Kband : ℝ)) c Cf ell Sent k

/-- The exact little-o label conclusion of the physical prevector theorem
makes the actual rough lower remainder vanish for this same label sequence.
Source: `07-comparators.tex`, lines 255--281 and 585--651, adc7f124. -/
theorem tendsto_roughLowerRemainder_of_label_dimension
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
      (fun k : ℕ => (k : ℝ))) (Kband : ℕ) (c Cf : ℝ) :
    Tendsto (roughLowerRemainder Kband c Cf ell Sent) atTop (𝓝 0) :=
  tendsto_roughLowerRemainderAtWeight_of_label_dimension
    ell Sent hdim Kband (4 / (Kband : ℝ)) c Cf

/-- For any positive error allowance, one replica threshold controls the
remainder before a copy number or any actual interpolation is selected.
Source: the replica-limit step in `08-scanner.tex`, lines 755--769, adc7f124. -/
theorem exists_roughLowerRemainder_threshold
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
      (fun k : ℕ => (k : ℝ))) (Kband : ℕ) (c Cf εrep : ℝ) (hεrep : 0 < εrep) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → roughLowerRemainder Kband c Cf ell Sent k < εrep := by
  have hlim := tendsto_roughLowerRemainder_of_label_dimension ell Sent hdim Kband c Cf
  exact eventually_atTop.1 (hlim.eventually (gt_mem_nhds hεrep))

end TNLean.PEPS.AreaLaw.Scan
