/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateCoreCounts
import TNLean.PEPS.AreaLaw.Geometry.DyadicWeightedSum
import TNLean.PEPS.AreaLaw.Geometry.CappedDyadicPartitionByScale

/-!
# Weighted dyadic covering of the actual template core

The actual capped partition of a template has a bounded sum of side lengths
to every power `1 + e`, for `e > 0`. The cap and lower-scale counts come from
`TemplateCoreCounts`; the finite arithmetic comes from `DyadicWeightedSum`.
No counting bound, separation or entropy conclusion is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 9.4, `08-scanner.tex`, lines 662–664, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The weighted sum over the actual capped template core partition, with an
explicit exponent-dependent constant. Source: Lemma 9.4, lines 662–664. -/
theorem Template.sum_rpow_cappedDyadicPartition_core_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (K : ℕ)
    (hlo : 2 ^ K ≤ s₀) (hhi : s₀ < 2 ^ (K + 1)) (e : ℝ) (he : 0 < e) :
    ∑ c ∈ cappedDyadicPartition T.points K, ((2 : ℝ) ^ c.1) ^ (1 + e) ≤
      (18 + 4 / ((2 : ℝ) ^ e - 1)) * n * (s₀ : ℝ) ^ e := by
  exact (sum_rpow_cappedDyadicPartition_le T.points K s₀ he (A := 18 * n) (B := 4 * n)
    (by positivity) hlo
    (by exact_mod_cast T.card_cappedDyadicPartition_at_cap_le (by linarith) K hhi)
    fun k hk ↦ by exact_mod_cast T.card_cappedDyadicPartition_below_cap_le hC K k hlo hk).trans_eq
    (by ring)

end TNLean.PEPS.AreaLaw.Geometry
