/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RectangleShellCounts
import TNLean.PEPS.AreaLaw.Geometry.CappedDyadicPartitionByScale
import TNLean.PEPS.AreaLaw.Geometry.DyadicWeightedSum

/-!
# Weighted dyadic covering of a rectangle shell

The actual capped partition of a dilated rectangle shell has a bound on
the sum of its side lengths to any power strictly greater than one.
The estimate follows from the cap and lower-scale counting bounds,
finite geometric summation, and the comparison of the cap with L.
It applies to thin rectangles and negative coordinates, including cap zero
and the empty shell.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, proof of Proposition 9.5, 08-scanner.tex, lines 717–729,
at openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
This is the geometric weighted covering estimate, prior to the entropy
estimate and the one-step entropy improvement.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw

/-- The sum of side lengths to the power `1 + e` in the actual capped
partition of a weak-rectangle shell. Source: `08-scanner.tex`, lines 717--729.
-/
theorem IntRect.sum_rpow_cappedDyadicPartition_shell_le
    (Q : IntRect) (j L K : ℕ) (hj : j ≤ L) (hL : L ≤ Q.size)
    (hlo : 2 ^ K ≤ L) (hhi : L < 2 ^ (K + 1)) (e : ℝ) (he : 0 < e) :
    (∑ c ∈ Geometry.cappedDyadicPartition
      ((Q.dilate j).toFinset \ Q.toFinset) K,
      ((2 : ℝ) ^ c.1) ^ (1 + e)) ≤
        (24 + 64 / ((2 : ℝ) ^ e - 1)) * (Q.size : ℝ) * (L : ℝ) ^ e := by
  exact (Geometry.sum_rpow_cappedDyadicPartition_le _ K L he
    (A := 24 * (Q.size : ℝ)) (B := 64 * (Q.size : ℝ))
    (by positivity) hlo
    (by exact_mod_cast Q.card_cappedDyadicPartition_shell_at_cap_le j L K hj hL hhi)
    fun k hk ↦ by
      exact_mod_cast Q.card_cappedDyadicPartition_shell_below_cap_le j K k (hj.trans hL) hk
        ((Nat.pow_le_pow_right (n := 2) (by decide) (Nat.succ_le_of_lt hk)).trans
          (hlo.trans hL))).trans_eq (by ring)

end TNLean.PEPS.AreaLaw
