/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Polygons.Squares.CappedDyadicPartition
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import QICLean.ManyBody.Sites.Lattice.IntegerRectangle
import TNLean.PEPS.AreaLaw.Polygons.Squares.MixedDyadicSquares

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

## Weighted dyadic covering of a rectangle shell

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

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.quotient_interval_card`: cardinality of integer quotient intervals.
* `ManyBody.IntRect.card_mixedDyadicIndices_toFinset_le`: mixed dyadic cells of an integer
  rectangle.
-/

section QuotientIntervals

/-!
## Cardinality of integer quotient intervals

For integers a ≤ b and a positive integer u, the number of integers from
⌊a/u⌋ through ⌊b/u⌋, multiplied by u, is at most b - a + 2u. The estimate
holds for negative endpoints as well as positive ones. It bounds the number
of rows and columns met by dyadic cells in the geometric covering argument.

### References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, Lemma 9.4, the boundary-line count in `08-scanner.tex`, lines 622–649,
and its rectangle application in the proof of Proposition 9.5, lines 717–729,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- For a positive divisor, the inclusive quotient interval has total length
at most the endpoint displacement plus two divisor lengths.
Auxiliary arithmetic estimate for the proofs of Lemma 9.4 and Proposition 9.5,
the boundary-line count in
`08-scanner.tex`, lines 622–649 and 717–729. -/
theorem quotient_interval_card (a b u : ℤ) (hu : 0 < u) (hab : a ≤ b) :
    u * ((Finset.Icc (a / u) (b / u)).card : ℤ) ≤ b - a + 2 * u := by
  have hdiv := Int.ediv_le_ediv hu hab
  rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
  have ha := Int.lt_ediv_add_one_mul_self a hu
  have hb := Int.ediv_mul_le b (ne_of_gt hu)
  nlinarith

end TNLean.PEPS.AreaLaw.Geometry

end QuotientIntervals

section RectangleMixedSquares

/-!
## Mixed dyadic cells of an integer rectangle

A mixed cell meets both the rectangle and its complement. Its index lies
on one of the two endpoint columns or endpoint rows. Counting these four
lines gives a bound independent of the rectangle's aspect ratio.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, the boundary-line count in the proof of Proposition 9.5,
`08-scanner.tex`, lines 717–729, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

open ManyBody (IntRect)

namespace TNLean.PEPS.AreaLaw

/-- Total side length of mixed cells of a native rectangle is bounded by
its four boundary lines. No aspect-ratio assumption is needed.
Source: the rectangle boundary-line count in `08-scanner.tex`, lines 717–729,
in the proof of Proposition 9.5 (`prop:small-box`). -/
theorem _root_.ManyBody.IntRect.card_mixedDyadicIndices_toFinset_le (Q : IntRect) (k : ℕ) :
    2 ^ k * (Geometry.mixedDyadicIndices Q.toFinset k).card ≤
      4 * Q.size + 8 * 2 ^ k := by
  let u : ℤ := 2 ^ k
  have hu : 0 < u := by dsimp [u]; positivity
  have hboundary : Geometry.mixedDyadicIndices Q.toFinset k ⊆
      ({Q.x₀ / u, Q.x₁ / u} : Finset ℤ).product (Finset.Icc (Q.y₀ / u) (Q.y₁ / u)) ∪
        (Finset.Icc (Q.x₀ / u) (Q.x₁ / u)).product {Q.y₀ / u, Q.y₁ / u} := by
    intro z hz
    obtain ⟨⟨p, hp, hpQ⟩, r, hr, hrQ⟩ :=
      (Geometry.mem_mixedDyadicIndices Q.toFinset k z).mp hz
    obtain ⟨hpx₀, hpx₁, hpy₀, hpy₁⟩ := IntRect.mem_toFinset.mp hpQ
    have hpidx : p.1 / u = z.1 ∧ p.2 / u = z.2 :=
      Prod.mk.inj ((Geometry.mem_latticeDyadicCell k z p).mp hp)
    have hridx : r.1 / u = z.1 ∧ r.2 / u = z.2 :=
      Prod.mk.inj ((Geometry.mem_latticeDyadicCell k z r).mp hr)
    have hbox : Q.x₀ / u ≤ z.1 ∧ z.1 ≤ Q.x₁ / u ∧
        Q.y₀ / u ≤ z.2 ∧ z.2 ≤ Q.y₁ / u := by
      rw [← hpidx.1, ← hpidx.2]
      exact ⟨Int.ediv_le_ediv hu hpx₀, Int.ediv_le_ediv hu hpx₁,
        Int.ediv_le_ediv hu hpy₀, Int.ediv_le_ediv hu hpy₁⟩
    have hout : r.1 < Q.x₀ ∨ Q.x₁ < r.1 ∨ r.2 < Q.y₀ ∨ Q.y₁ < r.2 := by
      have hnot := mt IntRect.mem_toFinset.mpr hrQ
      omega
    simp only [Finset.product_eq_sprod, Finset.mem_union, Finset.mem_product, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_Icc]
    rcases hout with h | h | h | h
    all_goals have hd := Int.ediv_le_ediv hu (le_of_lt h)
    all_goals simp only [hridx] at hd
    all_goals omega
  have hcard := Finset.card_le_card hboundary
  have hunion := hcard.trans (Finset.card_union_le _ _)
  simp only [Finset.product_eq_sprod, Finset.card_product] at hunion
  have hcount : (Geometry.mixedDyadicIndices Q.toFinset k).card ≤
      2 * (Finset.Icc (Q.x₀ / u) (Q.x₁ / u)).card +
        2 * (Finset.Icc (Q.y₀ / u) (Q.y₁ / u)).card := by
    have hxp : ({Q.x₀ / u, Q.x₁ / u} : Finset ℤ).card ≤ 2 := Finset.card_le_two
    have hyp : ({Q.y₀ / u, Q.y₁ / u} : Finset ℤ).card ≤ 2 := Finset.card_le_two
    have hleft := Nat.mul_le_mul hxp
      (Nat.le_refl (Finset.Icc (Q.y₀ / u) (Q.y₁ / u)).card)
    have hright := Nat.mul_le_mul
      (Nat.le_refl (Finset.Icc (Q.x₀ / u) (Q.x₁ / u)).card) hyp
    have hsum := hunion.trans (Nat.add_le_add hleft hright)
    omega
  have hcountInt : ((Geometry.mixedDyadicIndices Q.toFinset k).card : ℤ) ≤
      2 * ((Finset.Icc (Q.x₀ / u) (Q.x₁ / u)).card : ℤ) +
        2 * ((Finset.Icc (Q.y₀ / u) (Q.y₁ / u)).card : ℤ) := by
    exact_mod_cast hcount
  have hm := mul_le_mul_of_nonneg_left hcountInt (le_of_lt hu)
  have hx := Geometry.quotient_interval_card Q.x₀ Q.x₁ u hu Q.hx
  have hy := Geometry.quotient_interval_card Q.y₀ Q.y₁ u hu Q.hy
  have hfinal : u * ((Geometry.mixedDyadicIndices Q.toFinset k).card : ℤ) ≤
      4 * (Q.size : ℤ) + 8 * u := by
    nlinarith only [hm, hx, hy, Q.width_le_size, Q.height_le_size]
  dsimp only [u] at hfinal
  exact_mod_cast hfinal

end TNLean.PEPS.AreaLaw

end RectangleMixedSquares

section RectangleShellCounts

open ManyBody (IntRect card_dilate_sdiff_le)

section

namespace TNLean.PEPS.AreaLaw

/-- Integer dilation adds twice the radius to the maximal side length.
Source: `02-initial.tex`, lines 222–231; `08-scanner.tex`, lines 717–729. -/
theorem _root_.ManyBody.IntRect.size_dilate (Q : IntRect) (j : ℕ) :
    (Q.dilate j).size = Q.size + 2 * j := by
  have hx := Q.hx
  have hy := Q.hy
  simp only [IntRect.size, IntRect.dilate]
  omega

/-- The cap-scale side budget for the actual partition of a rectangle shell.
Source: auxiliary covering estimate in the proof of Proposition 9.5,
`08-scanner.tex`, lines 717–729. -/
theorem _root_.ManyBody.IntRect.card_cappedDyadicPartition_shell_at_cap_le
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
theorem _root_.ManyBody.IntRect.card_cappedDyadicPartition_shell_below_cap_le
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

end

section

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw

/-- The sum of side lengths to the power `1 + e` in the actual capped
partition of a weak-rectangle shell. Source: `08-scanner.tex`, lines 717--729.
-/
theorem _root_.ManyBody.IntRect.sum_rpow_cappedDyadicPartition_shell_le
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

end

end RectangleShellCounts
