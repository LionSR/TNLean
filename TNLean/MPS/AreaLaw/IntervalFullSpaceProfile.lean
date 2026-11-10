/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalGenerators

/-!
# Dimension and recorded-rank bounds for full short intervals

A full short interval has its original orthonormal basis as a recorded
spanning family. This common leaf argument is shared by the viable-tree
constructions. Source: ALVV, arXiv:1602.08828v2, initialization,
lines 1650–1662. No viability premise is required for these size bounds.
-/

namespace TNLean.MPS.AreaLaw

/-- The full short interval satisfies the common dimension and recorded
rank bounds whenever its full dimension fits the leaf count. -/
theorem interval_top_dimension_and_rank_bounds
    {L q p r width count : ℕ} {xi : ℝ}
    (hq : 1 ≤ q) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hleaf : q ^ width ≤ count) (hshort : r - p ≤ width) :
    Module.finrank ℂ (⊤ : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) ≤ count ∧
      IsIntervalSpanWithRankBound L q p r count xi ⊤ := by
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) ≤ count := by
    calc
      _ = q ^ (interval L p r).card := by
        rw [finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
      _ ≤ q ^ width := Nat.pow_le_pow_right hq ((card_interval_le _ _).trans hshort)
      _ ≤ count := hleaf
  exact ⟨by simpa only [finrank_top] using hdim,
    isIntervalSpanWithRankBound_top hq hdim hxi0 hxi1⟩

end TNLean.MPS.AreaLaw
