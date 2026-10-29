/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CutMatrixGrowth

/-!
# Centered windows and the exact boundary alternative

A larger window can be centered at the same physical cut as its initial
window. If it does not fit, the actual vector has an exact cut-rank bound
from the smaller side of the chain. This alternative includes endpoint
cuts and chains shorter than the proposed window.

Source: the accuracy-dependent window choice in AKLV, arXiv:1301.1162v1,
lines 1503--1517. The boundary alternative is the elementary finite-dimensional
completion of that choice, not an independent area-law theorem.
-/

namespace TNLean.MPS.AreaLaw

/-- Exact left and right margins for a window centered at a prescribed cut. -/
theorem aklv_centered_window_iff {L k s : ℕ} (hk : k ≤ L) :
    (∃ a : ℕ, a + s / 2 = k ∧ a + s + 1 ≤ L) ↔
      s / 2 ≤ k ∧ s - s / 2 + 1 ≤ L - k := by
  constructor
  · rintro ⟨a, hcenter, hfit⟩
    omega
  · rintro ⟨hleft, hright⟩
    exact ⟨k - s / 2, by omega, by omega⟩

/-- Enlarging a window by an even number of sites preserves its central cut;
whenever the enlarged window fits, the original one fits as well. -/
theorem aklv_initial_window_of_enlarged {L a s m : ℕ}
    (ha : a + (s + 2 * m) + 1 ≤ L) :
    (a + m) + s / 2 = a + (s + 2 * m) / 2 ∧ (a + m) + s + 1 ≤ L := by
  omega

/-- Failure of the centered-window condition puts the cut near an endpoint.
The ceiling half-width is written as `s-s/2`, including odd widths. -/
theorem aklv_short_side_of_no_centered_window {L k s : ℕ} (hk : k ≤ L)
    (hfit : ¬ ∃ a : ℕ, a + s / 2 = k ∧ a + s + 1 ≤ L) :
    min k (L - k) ≤ s - s / 2 := by
  have hnot : ¬ (s / 2 ≤ k ∧ s - s / 2 + 1 ≤ L - k) := by
    rwa [← aklv_centered_window_iff hk]
  omega

/-- The actual coefficient rank is bounded by the dimension of the smaller
side. This uses only the two endpoint ranks and physical cut transport. -/
theorem aklv_rank_cutMatrix_le_pow_min {L q k : ℕ} (hk : k ≤ L)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    (cutMatrix Ω k).rank ≤ q ^ min k (L - k) := by
  have h := rank_cutMatrix_le_pow_min_mul Ω (a := 0) (b := L) (R := 1)
    (Nat.zero_le k) hk le_rfl (rank_cutMatrix_zero_le Ω)
    (rank_cutMatrix_le_one_of_le le_rfl Ω)
  simpa only [Nat.sub_zero, mul_one] using h

/-- Either the prescribed window fits at the cut, or the original vector
itself is an exact approximant with the corresponding boundary rank. -/
theorem aklv_centered_window_or_exact_rank {L q k s : ℕ} (hq : 1 ≤ q) (hk : k ≤ L)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    (∃ a : ℕ, a + s / 2 = k ∧ a + s + 1 ≤ L) ∨
      (cutMatrix Ω k).rank ≤ q ^ (s - s / 2) := by
  classical
  by_cases hfit : ∃ a : ℕ, a + s / 2 = k ∧ a + s + 1 ≤ L
  · exact Or.inl hfit
  · exact Or.inr ((aklv_rank_cutMatrix_le_pow_min hk Ω).trans
      (Nat.pow_le_pow_right hq (aklv_short_side_of_no_centered_window hk hfit)))

end TNLean.MPS.AreaLaw
