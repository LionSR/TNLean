/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RectangleMixedSquares

/-!
# Dyadic counts for rectangle shells

The actual capped maximal-contained partition of a rectangle shell has a
uniform side-length budget at each scale. The cap budget follows from the
area of the shell. Below the cap, the mixed-cell counts of the inner and
outer rectangles control the selected squares through their four-child
parents. The bounds are independent of aspect ratio and location.

These are auxiliary geometric estimates for the rectangle covering in the
proof of Proposition 9.5. They impose no safety condition on a physical cut.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, integer dilation in `02-initial.tex`, lines 222–231,
and the proof of Proposition 9.5 in `08-scanner.tex`, lines 717–729,
at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- Integer dilation adds twice the radius to the maximal side length.
Source: `02-initial.tex`, lines 222–231; `08-scanner.tex`, lines 717–729. -/
theorem IntRect.size_dilate (Q : IntRect) (j : ℕ) :
    (Q.dilate j).size = Q.size + 2 * j := by
  have hx := Q.hx
  have hy := Q.hy
  simp only [IntRect.size, IntRect.dilate]
  omega

/-- The cap-scale side budget for the actual partition of a rectangle shell.
Source: auxiliary covering estimate in the proof of Proposition 9.5,
`08-scanner.tex`, lines 717–729. -/
theorem IntRect.card_cappedDyadicPartition_shell_at_cap_le
    (Q : IntRect) (j L K : ℕ) (hj : j ≤ L) (hL : L ≤ Q.size)
    (hhi : L < 2 ^ (K + 1)) :
    2 ^ K * ((Geometry.cappedDyadicPartition
      ((Q.dilate j).toFinset \ Q.toFinset) K).filter (fun c ↦ c.1 = K)).card ≤
      24 * Q.size := by
  have harea := card_dilate_sdiff_le Q (d := j) (k := j) (Nat.le_refl j)
  simp only [Nat.sub_self, IntRect.dilate_zero] at harea
  have hwidth : Q.size + 2 * j ≤ 3 * Q.size := by omega
  have harea12 := harea.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hj) hwidth)
  have hcap := Geometry.card_cappedDyadicPartition_at_cap_le
    ((Q.dilate j).toFinset \ Q.toFinset) K
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow] at hcap
  rw [pow_succ] at hhi
  have hLbudget := Nat.mul_le_mul_left (12 * Q.size) (Nat.le_of_lt hhi)
  have hbound : 2 ^ K * (2 ^ K * ((Geometry.cappedDyadicPartition
      ((Q.dilate j).toFinset \ Q.toFinset) K).filter (fun c ↦ c.1 = K)).card) ≤
      2 ^ K * (24 * Q.size) := by
    nlinarith only [hcap, harea12, hLbudget]
  exact Nat.le_of_mul_le_mul_left hbound (by positivity)

/-- The side budget below the cap for the actual partition of a rectangle shell.
Source: auxiliary covering estimate in the proof of Proposition 9.5,
`08-scanner.tex`, lines 717–729. -/
theorem IntRect.card_cappedDyadicPartition_shell_below_cap_le
    (Q : IntRect) (j K k : ℕ) (hj : j ≤ Q.size) (hk : k < K)
    (hscale : 2 ^ (k + 1) ≤ Q.size) :
    2 ^ k * ((Geometry.cappedDyadicPartition
      ((Q.dilate j).toFinset \ Q.toFinset) K).filter (fun c ↦ c.1 = k)).card ≤
      64 * Q.size := by
  have hdiff := Geometry.card_mixedDyadicIndices_sdiff_le
    (Q.dilate j).toFinset Q.toFinset (k + 1)
  have houter := (Q.dilate j).card_mixedDyadicIndices_toFinset_le (k + 1)
  have hinner := Q.card_mixedDyadicIndices_toFinset_le (k + 1)
  rw [IntRect.size_dilate] at houter
  have hdiffWeighted := Nat.mul_le_mul_left (2 ^ (k + 1)) hdiff
  have hparents : 2 ^ (k + 1) * (Geometry.mixedDyadicIndices
      ((Q.dilate j).toFinset \ Q.toFinset) (k + 1)).card ≤ 32 * Q.size := by
    nlinarith only [hdiffWeighted, houter, hinner, hj, hscale]
  have hchildren := Geometry.card_cappedDyadicPartition_below_cap_le
    ((Q.dilate j).toFinset \ Q.toFinset) K k hk
  rw [pow_succ] at hparents
  have hweightedChildren := Nat.mul_le_mul_left (2 ^ k) hchildren
  nlinarith only [hweightedChildren, hparents]

end TNLean.PEPS.AreaLaw
