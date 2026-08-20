/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Wielandt.SpanGrowth.NonzeroTraceProduct
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Compatibility wrappers for bounded nonzero-trace words

The finite-family results are defined in namespace `Kraus`. This module preserves
established tensor-network theorem names and statement shapes.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Compatibility wrapper for the coarse cumulative-span bound. -/
theorem cumulativeSpan_eq_top_of_isNormal_bound [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    cumulativeSpan A (D ^ 2) = ⊤ := by
  obtain ⟨N, _, hN⟩ := hN
  exact Kraus.cumulativeSpan_eq_top_of_wordSpan_eq_top_bound A hN

/-- Compatibility wrapper for the coarse cumulative-span form of Lemma 1. -/
theorem cumulativeSpan_eq_top [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    cumulativeSpan A (D ^ 2) = ⊤ := by
  obtain ⟨N, _, hN⟩ := hN
  exact Kraus.cumulativeSpan_eq_top A hN

/-- Compatibility wrapper for the coarse nonzero-trace word bound. -/
theorem exists_nonzero_trace_word [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    ∃ w : List (Fin d),
      w.length ≤ D ^ 2 ∧ Matrix.trace (evalWord A w) ≠ 0 := by
  obtain ⟨N, _, hN⟩ := hN
  exact Kraus.exists_nonzero_trace_word A hN

/-- Compatibility wrapper for the one-step cumulative-span dimension bound. -/
theorem finrank_cumulativeSpan_one_ge_wordSpan_one (A : MPSTensor d D) :
    Module.finrank ℂ (cumulativeSpan A 1) ≥
      Module.finrank ℂ (wordSpan A 1) :=
  Kraus.finrank_cumulativeSpan_one_ge_wordSpan_one A

/-- Compatibility wrapper for the sharp cumulative-span bound. -/
theorem cumulativeSpan_eq_top_of_isNormal_sharp [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    cumulativeSpan A (D ^ 2 - Module.finrank ℂ (wordSpan A 1) + 1) = ⊤ := by
  obtain ⟨N, _, hN⟩ := hN
  exact Kraus.cumulativeSpan_eq_top_of_wordSpan_eq_top_sharp A hN

/-- Compatibility wrapper for the sharp nonzero-trace word bound. -/
theorem exists_nonzero_trace_word_sharp [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    ∃ w : List (Fin d),
      w.length ≤ D ^ 2 - Module.finrank ℂ (wordSpan A 1) + 1 ∧
        Matrix.trace (evalWord A w) ≠ 0 := by
  obtain ⟨N, _, hN⟩ := hN
  exact Kraus.exists_nonzero_trace_word_sharp A hN

/-- Compatibility wrapper for the positive-length sharp nonzero-trace word bound. -/
theorem exists_nonzero_trace_word_sharp_pos [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    ∃ w : List (Fin d),
      1 ≤ w.length ∧
      w.length ≤ D ^ 2 - Module.finrank ℂ (wordSpan A 1) + 1 ∧
        Matrix.trace (evalWord A w) ≠ 0 := by
  obtain ⟨N, hNpos, hN⟩ := hN
  exact Kraus.exists_nonzero_trace_word_sharp_pos A hN hNpos

end MPSTensor
