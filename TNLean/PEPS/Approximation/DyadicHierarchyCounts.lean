/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TNLean.PEPS.Approximation.DyadicAnchors

/-!
# Counting the padded dyadic hierarchy

Let `N = 2 ^ k` be the padded side, with `L ≤ N < 2 L`. The dyadic hierarchy consists of the
aligned squares of `[0, N] ^ 2` of side `n = 2 ^ j`, `0 ≤ j ≤ k`, including the root square;
there are `4 ^ (k - j)` of them at scale `j`. Each non-root square is repainted once, when
passing from the assignment by `2n`-squares to the assignment by `n`-squares, and at scale `j`
there are `(2 ^ (k - j) + 1) ^ 2` grid corners, the possible true vertices whose holes are
resized on entering a level.

This file proves the geometric counts behind Proposition 7.1 (`prop:protocol`), items 1–3:

* the hierarchy has `(4 ^ (k + 1) - 1) / 3` squares, hence `O(L ^ 2)`;
* the repaintings and the junctions over all scales number `O(N ^ 2) = O(L ^ 2)`, so `M` times
  their number is `O(M L ^ 2)`, in particular at most `C M L ^ 3`; the number of changes per
  repainting, which counts gates of the protocol, is not treated here;
* the integer address `eq:geometry-addresses` of a square, the dyadic anchor `dyadicAnchor` of
  the routing step (§8.3, `eq:anchors`), lies in `{0, …, N - 1}`, and, one coordinate at a time,
  blocks at scales `j' ≤ j + 1` whose closed intervals are within distance `g` have address
  coordinates within `g + 3 · 2 ^ j`, so the owners of a repainted block, of its neighbors and
  of their parents are at the same or adjacent scales and at address distance `O(n)`;
* one coordinate of the count of blocks meeting an interval, an ingredient of the bounded
  lifetime participation. The guide part of the active-label invariant is in
  `TNLean.PEPS.Approximation.DyadicLevelSchedule`; its part on tags is not treated here.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: Proposition 7.1
  `prop:protocol` (lines 12–53), the hierarchy (lines 62–67), the addresses
  `eq:geometry-addresses` (lines 633–647), and the counts (lines 649–652).
-/

namespace TNLean.PEPS.Approximation

open Finset

/-! ### Squares of the hierarchy -/

/-- The squares of the dyadic hierarchy of `[0, 2 ^ k] ^ 2`: a scale `j ≤ k` and two block
indices below `2 ^ (k - j)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:63–67`. -/
abbrev DyadicSquare (k : ℕ) : Type := Σ j : Fin (k + 1), Fin (2 ^ (k - j)) × Fin (2 ^ (k - j))

/-- The grid corners at scale `j` of `[0, 2 ^ k] ^ 2`: two indices at most `2 ^ (k - j)`. These
are the possible true vertices of a guide uniform on `2 ^ j`-squares.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:321–322, 508, 529–541`. -/
abbrev DyadicJunction (k : ℕ) : Type :=
  Σ j : Fin (k + 1), Fin (2 ^ (k - j) + 1) × Fin (2 ^ (k - j) + 1)

private theorem three_mul_sum_range_four_pow_add_one (m : ℕ) :
    3 * ∑ i ∈ range m, 4 ^ i + 1 = 4 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, pow_succ]; omega

private theorem sum_fin_four_pow_sub (k : ℕ) :
    ∑ j : Fin (k + 1), 4 ^ (k - (j : ℕ)) = ∑ i ∈ range (k + 1), 4 ^ i := by
  rw [Fin.sum_univ_eq_sum_range (fun j => 4 ^ (k - j)) (k + 1)]
  exact sum_range_reflect (fun i => 4 ^ i) (k + 1)

/-- The number of squares of the hierarchy is `(4 ^ (k + 1) - 1) / 3`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:19–20, 649–652`. -/
theorem three_mul_card_dyadicSquare_add_one (k : ℕ) :
    3 * Fintype.card (DyadicSquare k) + 1 = 4 ^ (k + 1) := by
  have h : Fintype.card (DyadicSquare k) = ∑ j : Fin (k + 1), 4 ^ (k - (j : ℕ)) := by
    rw [Fintype.card_sigma]
    refine sum_congr rfl fun j _ => ?_
    rw [Fintype.card_prod, Fintype.card_fin, ← mul_pow]
    norm_num
  rw [h, sum_fin_four_pow_sub, three_mul_sum_range_four_pow_add_one]

/-- The number of grid corners over all scales is at most `4 / 3` of `4 ^ (k + 1)`. -/
theorem three_mul_card_dyadicJunction_le (k : ℕ) :
    3 * Fintype.card (DyadicJunction k) ≤ 4 * 4 ^ (k + 1) := by
  have h : Fintype.card (DyadicJunction k) = ∑ j : Fin (k + 1), (2 ^ (k - (j : ℕ)) + 1) ^ 2 := by
    rw [Fintype.card_sigma]
    refine sum_congr rfl fun j _ => ?_
    rw [Fintype.card_prod, Fintype.card_fin, sq]
  have hle : ∑ j : Fin (k + 1), (2 ^ (k - (j : ℕ)) + 1) ^ 2 ≤
      4 * ∑ j : Fin (k + 1), 4 ^ (k - (j : ℕ)) := by
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    have h1 : 1 ≤ 2 ^ (k - (j : ℕ)) := Nat.one_le_two_pow
    rw [show (4 : ℕ) ^ (k - (j : ℕ)) = 2 ^ (k - (j : ℕ)) * 2 ^ (k - (j : ℕ)) by
      rw [← mul_pow]; norm_num]
    nlinarith
  rw [h]
  have := three_mul_sum_range_four_pow_add_one (k + 1)
  rw [← sum_fin_four_pow_sub] at this
  linarith

private theorem four_pow_lt_of_two_pow_lt {k L : ℕ} (hk : 2 ^ k < 2 * L) : 4 ^ k < L ^ 2 * 4 := by
  have h : 4 ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  rw [h]
  nlinarith [Nat.zero_le (2 ^ k)]

/-- **`O(L ^ 2)` parties.** With `2 ^ k < 2 L`, the hierarchy has fewer than `16 L ^ 2 / 3`
squares.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 1,
`06-geometry.tex:19–20`, and `06-geometry.tex:649–652`. -/
theorem three_mul_card_dyadicSquare_lt {k L : ℕ} (hk : 2 ^ k < 2 * L) :
    3 * Fintype.card (DyadicSquare k) < 16 * L ^ 2 := by
  have h1 := three_mul_card_dyadicSquare_add_one k
  have h2 := four_pow_lt_of_two_pow_lt hk
  rw [pow_succ] at h1
  linarith

/-- **Schedule length.** If each repainting of a non-root square and each junction resize uses
at most `M` changes, the schedule has at most `80 M L ^ 2 / 3` changes: three times `M` times
the number of squares plus junctions is at most `80 M L ^ 2`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 2,
`06-geometry.tex:25`, and `06-geometry.tex:576–579, 649–652`. -/
theorem three_mul_schedule_le {k L : ℕ} (hk : 2 ^ k < 2 * L) (M : ℕ) :
    3 * (M * (Fintype.card (DyadicSquare k) + Fintype.card (DyadicJunction k))) ≤
      80 * M * L ^ 2 := by
  have h1 := three_mul_card_dyadicSquare_add_one k
  have h2 := three_mul_card_dyadicJunction_le k
  have h3 := four_pow_lt_of_two_pow_lt hk
  rw [pow_succ] at h1 h2
  have : 3 * (Fintype.card (DyadicSquare k) + Fintype.card (DyadicJunction k)) ≤ 80 * L ^ 2 := by
    linarith
  calc 3 * (M * (Fintype.card (DyadicSquare k) + Fintype.card (DyadicJunction k)))
      = M * (3 * (Fintype.card (DyadicSquare k) + Fintype.card (DyadicJunction k))) := by ring
    _ ≤ M * (80 * L ^ 2) := Nat.mul_le_mul_left M this
    _ = 80 * M * L ^ 2 := by ring

/-- **Cubic schedule bound.** The same count is at most `80 M L ^ 3 / 3`, the form `C L ^ 3` of
Proposition 7.1, item 2.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 2,
`06-geometry.tex:25`. -/
theorem three_mul_schedule_le_cube {k L : ℕ} (hk : 2 ^ k < 2 * L) (M : ℕ) :
    3 * (M * (Fintype.card (DyadicSquare k) + Fintype.card (DyadicJunction k))) ≤
      80 * M * L ^ 3 := by
  refine (three_mul_schedule_le hk M).trans (Nat.mul_le_mul_left _ ?_)
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  · exact Nat.pow_le_pow_right hL (by norm_num)

/-! ### Addresses -/

/-- The addresses of the hierarchy of `[0, 2 ^ k] ^ 2`, the dyadic anchors of its blocks, lie in
`{0, …, 2 ^ k - 1}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-addresses`,
`06-geometry.tex:633–646`. -/
theorem dyadicAnchor_lt_two_pow {k j r : ℕ} (hj : j ≤ k) (hr : r < 2 ^ (k - j)) :
    dyadicAnchor j r < 2 ^ k := by
  refine dyadicAnchor_lt ?_
  calc 2 ^ j * (r + 1) ≤ 2 ^ j * 2 ^ (k - j) := Nat.mul_le_mul_left _ hr
    _ = 2 ^ k := by rw [← pow_add, Nat.add_sub_cancel' hj]

/-- **Address locality.** If the closed interval of a block of side `2 ^ j` starts within `g`
after the end of a block of side `2 ^ j'`, then its address exceeds the other address by less
than `g + 2 ^ j + 2 ^ j'`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:585–588, 643–645`. -/
theorem dyadicAnchor_lt_add {j r j' r' g : ℕ} (h : 2 ^ j * r ≤ 2 ^ j' * r' + 2 ^ j' + g) :
    dyadicAnchor j r < dyadicAnchor j' r' + g + 2 ^ j + 2 ^ j' := by
  have h1 := dyadicAnchor_mem_block j r
  have h2 := dyadicAnchor_mem_block j' r'
  rw [mul_add, mul_one] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Address coordinates of nearby blocks at scales `j' ≤ j + 1`.** If two blocks of sides
`2 ^ j` and `2 ^ j'`, with `j' ≤ j + 1`, have closed intervals within distance `g` in one
coordinate, their address coordinates differ by less than `g + 3 · 2 ^ j`. It is an ingredient
of Proposition 7.1, item 3; see `dyadicAnchor_dist_lt_of_adjacent` for the owners of a
repainting.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 3,
`06-geometry.tex:34–37`, and `06-geometry.tex:643–645`. -/
theorem dyadicAnchor_dist_lt {j r j' r' g : ℕ} (hj : j' ≤ j + 1)
    (h : 2 ^ j * r ≤ 2 ^ j' * r' + 2 ^ j' + g) (h' : 2 ^ j' * r' ≤ 2 ^ j * r + 2 ^ j + g) :
    dyadicAnchor j r < dyadicAnchor j' r' + g + 3 * 2 ^ j ∧
      dyadicAnchor j' r' < dyadicAnchor j r + g + 3 * 2 ^ j := by
  have hp : 2 ^ j' ≤ 2 * 2 ^ j := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right two_pos hj
  have a := dyadicAnchor_lt_add h
  have b := dyadicAnchor_lt_add h'
  constructor <;> linarith

/-- **Parties of a repainting, one coordinate.** Let two blocks of side `2 ^ j` have adjacent or
equal indices `q, q'`. Each of them, or its parent of side `2 ^ (j + 1)`, has an address
coordinate within `3 · 2 ^ (j + 1)` of the other's: the owners and old owners of a repainted
block and of its neighbors are at the same or adjacent scales and at address distance `O(n)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 3,
`06-geometry.tex:34–37`, and `06-geometry.tex:585–592, 643–645`. -/
theorem dyadicAnchor_dist_lt_of_adjacent {j q q' : ℕ} (hq : q ≤ q' + 1) (hq' : q' ≤ q + 1)
    {j₁ a₁ j₂ a₂ : ℕ} (h₁ : (j₁ = j ∧ a₁ = q) ∨ (j₁ = j + 1 ∧ a₁ = q / 2))
    (h₂ : (j₂ = j ∧ a₂ = q') ∨ (j₂ = j + 1 ∧ a₂ = q' / 2)) :
    dyadicAnchor j₁ a₁ < dyadicAnchor j₂ a₂ + 3 * 2 ^ (j + 1) ∧
      dyadicAnchor j₂ a₂ < dyadicAnchor j₁ a₁ + 3 * 2 ^ (j + 1) := by
  have hP : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
  have hP0 : 0 < 2 ^ j := pow_pos two_pos j
  -- each party's closed interval contains the block's own interval `[2 ^ j q, 2 ^ j (q + 1)]`
  have hint : ∀ {i a q : ℕ}, (i = j ∧ a = q) ∨ (i = j + 1 ∧ a = q / 2) →
      2 ^ i * a ≤ 2 ^ j * q ∧ 2 ^ j * q + 2 ^ j ≤ 2 ^ i * a + 2 ^ i ∧ i ≤ j + 1 ∧
        2 ^ i ≤ 2 ^ (j + 1) := by
    rintro i a q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨le_rfl, le_rfl, Nat.le_succ _, Nat.pow_le_pow_right two_pos (Nat.le_succ _)⟩
    · have h1 : 2 * (q / 2) ≤ q := Nat.mul_div_le q 2
      have h2 : q < 2 * (q / 2) + 2 := by omega
      refine ⟨?_, ?_, le_rfl, le_rfl⟩
      · rw [hP]; nlinarith [Nat.mul_le_mul_left (2 ^ j) h1]
      · rw [hP]; nlinarith [Nat.mul_le_mul_left (2 ^ j) h2]
  obtain ⟨a1, b1, c1, d1⟩ := hint h₁
  obtain ⟨a2, b2, c2, d2⟩ := hint h₂
  have e1 : 2 ^ j * q ≤ 2 ^ j * q' + 2 ^ j := by nlinarith
  have e2 : 2 ^ j * q' ≤ 2 ^ j * q + 2 ^ j := by nlinarith
  have k1 := dyadicAnchor_lt_add (j := j₁) (r := a₁) (j' := j₂) (r' := a₂) (g := 0) (by omega)
  have k2 := dyadicAnchor_lt_add (j := j₂) (r := a₂) (j' := j₁) (r' := a₁) (g := 0) (by omega)
  constructor <;> omega

/-! ### Bounded lifetime incidence -/

/-- **Blocks near a block, one coordinate.** The blocks of side `b` (indices `r < M`) whose
closed intervals `[b r, b (r + 1)]` meet `[V, U]` number at most `⌊U / b⌋ + 2 - ⌊V / b⌋`. This is
the one-coordinate counting step: applied in each coordinate with `b ∈ {m, m / 2}` and
`U - V = O(m)`, it bounds by a constant the repaintings and junctions at levels `m` and `m / 2`
within distance `O(m)` of a block of side `m`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:611–618`: “At these scales
there are only a fixed number of repaintings or junctions within distance `O(m)` of its
block.” -/
theorem card_blocks_meeting_le {b : ℕ} (hb : 0 < b) (U V M : ℕ) :
    ((range M).filter fun r => V ≤ b * (r + 1) ∧ b * r ≤ U).card ≤ U / b + 2 - V / b := by
  calc ((range M).filter fun r => V ≤ b * (r + 1) ∧ b * r ≤ U).card
      ≤ (Icc (V / b) (U / b + 1)).card := by
        refine card_le_card_of_injOn (· + 1) ?_ ?_
        · intro r hr
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr
          simp only [coe_Icc, Set.mem_Icc]
          refine ⟨Nat.div_le_of_le_mul hr.2.1, ?_⟩
          have : r ≤ U / b := (Nat.le_div_iff_mul_le hb).2 (by rw [mul_comm]; exact hr.2.2)
          omega
        · intro r _ r' _ h
          simpa using h
    _ = U / b + 2 - V / b := by rw [Nat.card_Icc]

end TNLean.PEPS.Approximation
