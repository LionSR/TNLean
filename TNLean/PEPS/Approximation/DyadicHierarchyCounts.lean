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
* the repaintings and the junctions over all scales number `O(N ^ 2) = O(L ^ 2)`, so a schedule
  using a uniformly bounded number of changes per repainting and per junction has `O(L ^ 2)`,
  in particular at most `C L ^ 3`, changes;
* the integer address `eq:geometry-addresses` of a square lies in the square and in
  `{0, …, N - 1}`, and squares at the same or adjacent scales whose closed coordinate intervals
  are within distance `g` have addresses within `g + 3 n` of each other.

The address coincides with the dyadic anchor of the routing step (§8.3, `eq:anchors`); the two
definitions are to be unified when that development lands.

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

theorem three_mul_sum_range_four_pow_add_one (m : ℕ) : 3 * ∑ i ∈ range m, 4 ^ i + 1 = 4 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, pow_succ]; omega

theorem sum_fin_four_pow_sub (k : ℕ) :
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

theorem four_pow_lt_of_two_pow_lt {k L : ℕ} (hk : 2 ^ k < 2 * L) : 4 ^ k < L ^ 2 * 4 := by
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
at most `M` changes, the schedule has fewer than `80 M L ^ 2 / 3` changes, in particular at
most `27 M L ^ 3` for `L ≥ 1`.

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

theorem three_mul_schedule_le_cube {k L : ℕ} (hk : 2 ^ k < 2 * L) (M : ℕ) :
    3 * (M * (Fintype.card (DyadicSquare k) + Fintype.card (DyadicJunction k))) ≤
      80 * M * L ^ 3 := by
  refine (three_mul_schedule_le hk M).trans (Nat.mul_le_mul_left _ ?_)
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  · exact Nat.pow_le_pow_right hL (by norm_num)

/-! ### Addresses -/

/-- One coordinate of the integer address of a square of side `2 ^ j` with block index `r`:
`2 ^ j r + 2 ^ (j - 1)` for `j ≥ 1`, and `r` for `j = 0`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-addresses`,
`06-geometry.tex:633–642`. -/
def squareAddress (j r : ℕ) : ℕ := if j = 0 then r else 2 ^ j * r + 2 ^ (j - 1)

/-- The address lies in its square: `2 ^ j r ≤ a < 2 ^ j r + 2 ^ j`. -/
theorem squareAddress_mem (j r : ℕ) :
    2 ^ j * r ≤ squareAddress j r ∧ squareAddress j r < 2 ^ j * r + 2 ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [squareAddress]
  · have hlt : 2 ^ (j - 1) < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simp only [squareAddress, hj.ne', ite_false]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hlt _⟩

/-- The addresses of the hierarchy of `[0, 2 ^ k] ^ 2` lie in `{0, …, 2 ^ k - 1}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:645–646`. -/
theorem squareAddress_lt {k j r : ℕ} (hj : j ≤ k) (hr : r < 2 ^ (k - j)) :
    squareAddress j r < 2 ^ k := by
  have h := (squareAddress_mem j r).2
  have : 2 ^ j * r + 2 ^ j ≤ 2 ^ k := by
    calc 2 ^ j * r + 2 ^ j = 2 ^ j * (r + 1) := by ring
      _ ≤ 2 ^ j * 2 ^ (k - j) := Nat.mul_le_mul_left _ hr
      _ = 2 ^ k := by rw [← pow_add, Nat.add_sub_cancel' hj]
  omega

/-- **Address locality.** If the closed interval of a block of side `2 ^ j` starts within `g`
after the end of a block of side `2 ^ j'`, then its address exceeds the other address by less
than `g + 2 ^ j + 2 ^ j'`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:585–588, 643–645`. -/
theorem squareAddress_lt_add {j r j' r' g : ℕ} (h : 2 ^ j * r ≤ 2 ^ j' * r' + 2 ^ j' + g) :
    squareAddress j r < squareAddress j' r' + g + 2 ^ j + 2 ^ j' := by
  have h1 := squareAddress_mem j r
  have h2 := squareAddress_mem j' r'
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Same or adjacent scales at distance `O(n)`.** For blocks at the same or adjacent scales
`j' ≤ j + 1` whose closed intervals are within distance `g` in one coordinate, the address
coordinates differ by less than `g + 3 · 2 ^ j`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 3,
`06-geometry.tex:34–37`, and `06-geometry.tex:643–645`. -/
theorem squareAddress_dist_lt {j r j' r' g : ℕ} (hj : j' ≤ j + 1)
    (h : 2 ^ j * r ≤ 2 ^ j' * r' + 2 ^ j' + g) (h' : 2 ^ j' * r' ≤ 2 ^ j * r + 2 ^ j + g) :
    squareAddress j r < squareAddress j' r' + g + 3 * 2 ^ j ∧
      squareAddress j' r' < squareAddress j r + g + 3 * 2 ^ j := by
  have hp : 2 ^ j' ≤ 2 * 2 ^ j := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right two_pos hj
  have a := squareAddress_lt_add h
  have b := squareAddress_lt_add h'
  constructor <;> linarith

/-! ### Bounded lifetime incidence -/

/-- **Blocks near a block.** The blocks of side `b` (indices `r < M`) whose closed intervals
`[b r, b (r + 1)]` meet `[V, U]` number at most `⌊U / b⌋ + 2 - ⌊V / b⌋`. Applied in each
coordinate with `b ∈ {m, m / 2}` and `U - V = O(m)`, it bounds by a constant the repaintings and
junctions at levels `m` and `m / 2` within distance `O(m)` of a block of side `m`.

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
