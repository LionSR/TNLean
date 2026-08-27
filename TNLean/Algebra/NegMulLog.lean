/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# An identity for the negated multiplication by logarithm

This file supplies a generic identity for `Real.negMulLog` that is useful when
computing the entropy of a uniform distribution.
-/

namespace Real

/-- For `d ≠ 0`, `d * Real.negMulLog d⁻¹ = Real.log d`.

Upstreamable to Mathlib's `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`,
which has no lemma of this shape. -/
theorem mul_negMulLog_inv (d : ℝ) (hd : d ≠ 0) :
    d * Real.negMulLog d⁻¹ = Real.log d := by
  rw [Real.negMulLog]
  calc
    d * (-(d⁻¹) * Real.log (d⁻¹)) = -(d * d⁻¹ * Real.log (d⁻¹)) := by ring
    _ = -(1 * Real.log (d⁻¹)) := by field_simp [hd]
    _ = -Real.log (d⁻¹) := by simp
    _ = Real.log d := by rw [Real.log_inv, neg_neg]

end Real
