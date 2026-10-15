/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicEventScheduleOrder
import TNLean.PEPS.Approximation.DyadicLevelEvents

/-!
# The memory of the dyadic protocol between events

Before each event of the schedule of Proposition 7.1 of the polynomial-PEPS manuscript the main
guide is a block guide of a level, and the auxiliary sheets are idle initial copies or frozen
frames (`06-geometry.tex`, lines 82–133 and 653–667). This file fixes these memories along the
schedule:

* `resizedCorners i j`, `repaintedBlocks i j` : the grid corners of scale `j` whose holes have been
  resized, and the blocks of level `j` that have been repainted, by the first `i` events;
* `eventMain`, `mainState` : the main frame before the event number `i`, by the kind of that
  event: the guide uniform on the blocks of the scale of a resize, with the holes of the corners
  already resized of radius `h_n` and the others of radius `h_{2n}`, or the guide of the level of a
  repainting with the blocks already repainted, with holes of radius `h_n`; after the last event,
  the guide of the unit squares;
* `auxState`, `protocolState` : the auxiliary frames, frozen once their event is done and idle
  before, and the whole memory.

The holes of a block guide sit at grid corners of the closed root square
(`exists_index_of_isTrueVertex_levelGuide`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the hierarchy and the
  guides (lines 60–100), the holes and their resizes (lines 102–133), and the memory of the
  protocol (lines 653–667).
-/

noncomputable section

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k : ℕ}

/-! ### True vertices lie in the closed root square -/

/-- **True vertices of a level lie in the closed root square.** A true vertex of the sampled block
guide of a stage of the level `2 ^ j` is a grid corner `blockCorner (2 ^ j) Q` with
`0 ≤ Q.1, Q.2 ≤ 2 ^ (k - j)`: near any other grid corner all four blocks lie outside the root
square and carry the placeholder.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 62–67, 91–95 and 109–111. -/
theorem exists_index_of_isTrueVertex_levelGuide {j : ℕ} {done : Set (ℤ × ℤ)} {z : ℝ × ℝ}
    (hz : IsTrueVertex (levelGuide k j done) z) :
    ∃ Q : ℤ × ℤ, z = blockCorner ((2 : ℝ) ^ j) Q ∧ 0 ≤ Q.1 ∧ Q.1 ≤ 2 ^ (k - j) ∧ 0 ≤ Q.2 ∧
      Q.2 ≤ 2 ^ (k - j) := by
  classical
  have hn : (0 : ℝ) < 2 ^ j := by positivity
  have hG := (isDisplacedReading_levelGuide j done).isTrueVertex hz
  obtain ⟨Q, rfl⟩ := hG.eq_blockCorner hn
  refine ⟨Q, rfl, ?_⟩
  by_contra hQ
  refine (hasTwoLabelsNear_of_eventuallyEq_const (c := guidePlaceholder) ?_).not_isTrueVertex hG
  filter_upwards [ball_mem_nhds (blockCorner ((2 : ℝ) ^ j) Q) hn] with p hp
  have hd := mem_ball.1 hp
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hd
  obtain ⟨h1, h2⟩ := hd
  simp only [blockCorner] at h1 h2
  have hb (x : ℝ) (a : ℤ) (h : |x - 2 ^ j * a| < 2 ^ j) :
      a - 1 ≤ ⌊x / 2 ^ j⌋ ∧ ⌊x / 2 ^ j⌋ ≤ a := by
    rw [abs_lt] at h
    constructor
    · refine Int.le_floor.2 ?_
      rw [le_div_iff₀ hn, Int.cast_sub, Int.cast_one]
      nlinarith
    · refine Int.floor_le_iff.2 ?_
      rw [div_lt_iff₀ hn]
      nlinarith
  obtain ⟨a1, a2⟩ := hb _ _ h1
  obtain ⟨b1, b2⟩ := hb _ _ h2
  have hout : ¬InRoot ((2 : ℤ) ^ (k - j)) (blockIndex ((2 : ℝ) ^ j) p) := by
    simp only [InRoot, blockIndex]
    omega
  simp only [blockGuide, protocolLevelLabels, levelLabels, hout, ite_false]

/-! ### The repainted blocks and the resized corners -/

/-- The grid corners of scale `j` at the junctions of scale `j` among the first `i` events. -/
def resizedCorners (k i j : ℕ) : Set (ℝ × ℝ) :=
  {z | ∃ J : DyadicJunction k, (Sum.inr J : ProtocolEvent k) ∈ (eventSchedule k).take i ∧
    (J.1 : ℕ) = j ∧ z = blockCorner ((2 : ℝ) ^ j) J.index}

/-- The blocks of level `j` repainted among the first `i` events. -/
def repaintedBlocks (k i j : ℕ) : Set (ℤ × ℤ) :=
  {Q | ∃ S : DyadicSquare k, (Sum.inl S : ProtocolEvent k) ∈ (eventSchedule k).take i ∧
    (S.1 : ℕ) = j ∧ Q = S.index}

theorem take_succ_eventSchedule {i : ℕ} (hi : i < (eventSchedule k).length) :
    (eventSchedule k).take (i + 1) = (eventSchedule k).take i ++ [(eventSchedule k)[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  rfl

theorem resizedCorners_succ_inr {i : ℕ} (hi : i < (eventSchedule k).length) {J : DyadicJunction k}
    (he : (eventSchedule k)[i] = .inr J) :
    resizedCorners k (i + 1) J.1 =
      insert (blockCorner ((2 : ℝ) ^ (J.1 : ℕ)) J.index) (resizedCorners k i J.1) := by
  ext z
  simp only [resizedCorners, take_succ_eventSchedule hi, he, List.mem_append, List.mem_singleton,
    mem_ofPred_eq, mem_insert_iff]
  constructor
  · rintro ⟨J', h | h, hJ, rfl⟩
    · exact Or.inr ⟨J', h, hJ, rfl⟩
    · obtain rfl := Sum.inr_injective h
      exact Or.inl rfl
  · rintro (rfl | ⟨J', h, hJ, rfl⟩)
    · exact ⟨J, Or.inr rfl, rfl, rfl⟩
    · exact ⟨J', Or.inl h, hJ, rfl⟩

theorem repaintedBlocks_succ_inl {i : ℕ} (hi : i < (eventSchedule k).length) {S : DyadicSquare k}
    (he : (eventSchedule k)[i] = .inl S) :
    repaintedBlocks k (i + 1) S.1 = insert S.index (repaintedBlocks k i S.1) := by
  ext Q
  simp only [repaintedBlocks, take_succ_eventSchedule hi, he, List.mem_append,
    List.mem_singleton, mem_ofPred_eq, mem_insert_iff]
  constructor
  · rintro ⟨S', h | h, hS, rfl⟩
    · exact Or.inr ⟨S', h, hS, rfl⟩
    · obtain rfl := Sum.inl_injective h
      exact Or.inl rfl
  · rintro (rfl | ⟨S', h, hS, rfl⟩)
    · exact ⟨S, Or.inr rfl, rfl, rfl⟩
    · exact ⟨S', Or.inl h, hS, rfl⟩

end TNLean.PEPS.Approximation
