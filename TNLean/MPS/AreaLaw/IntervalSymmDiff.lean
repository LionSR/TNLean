/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Nat.Dist
import TNLean.MPS.AreaLaw.Basic

/-!
# Symmetric differences of chain intervals

The number of sites changed by moving the endpoints of an interval is at most
the sum of their displacements. Two cuts selected inside windows of length
`2 * ℓ` therefore change the middle region by at most `2 * ℓ` sites.
Intervals are clipped to the finite chain, including the empty chain.

## Main results

- `card_interval_symmDiff_le_dist`: the endpoint displacement bound.
- `card_two_window_middle_symmDiff_le`: the bound for the two middle-region
  conventions used in the two-cut operator-Schmidt-rank argument.

## References

- ALVV, arXiv:1602.08828v2, `item:small-sr`, lines 830–831, and
  `prop:Cheby-AGSP-eff`, lines 1311–1333.
-/

open scoped symmDiff

namespace TNLean.MPS.AreaLaw

/-- An interval changes at no more sites than the total movement of its two
endpoints. Supporting geometry for ALVV, arXiv:1602.08828v2,
`prop:Cheby-AGSP-eff`, lines 1331–1333. Intervals remain clipped to Fin L. -/
theorem card_interval_symmDiff_le_dist
    {L : ℕ} (a b c d : ℕ) :
    ((interval L a b) ∆ (interval L c d)).card ≤ Nat.dist a c + Nat.dist b d := by
  have hsub : (interval L a b) ∆ (interval L c d) ⊆
      interval L (min a c) (max a c) ∪ interval L (min b d) (max b d) := by
    intro i hi
    simp only [Finset.mem_symmDiff, mem_interval, Finset.mem_union] at hi ⊢
    omega
  calc
    _ ≤ (interval L (min a c) (max a c) ∪ interval L (min b d) (max b d)).card :=
      Finset.card_le_card hsub
    _ ≤ (interval L (min a c) (max a c)).card +
        (interval L (min b d) (max b d)).card := Finset.card_union_le _ _
    _ ≤ (max a c - min a c) + (max b d - min b d) :=
      Nat.add_le_add (card_interval_le _ _) (card_interval_le _ _)
    _ = Nat.dist a c + Nat.dist b d := by rw [Nat.dist_eq_max_sub_min, Nat.dist_eq_max_sub_min]

/-- Both source target blocks are within 2ℓ sites of the selected middle
block. ALVV, arXiv:1602.08828v2, `item:small-sr`, lines 830–831, and
`prop:Cheby-AGSP-eff`, lines 1311–1333. The value δ=0 gives the literal
block in Proposition 5.7; δ=1 gives the earlier pair of named cuts. -/
theorem card_two_window_middle_symmDiff_le
    {L a b ℓ : ℕ} (p s : Fin (2 * ℓ)) (δ : Fin 2) :
    ((interval L (a + p.val + 1) (b + s.val + 1)) ∆
      (interval L (a + ℓ + δ.val) (b + ℓ + 1))).card ≤ 2 * ℓ := by
  apply le_trans (card_interval_symmDiff_le_dist _ _ _ _)
  simp only [Nat.dist_eq_max_sub_min]
  omega

end TNLean.MPS.AreaLaw
