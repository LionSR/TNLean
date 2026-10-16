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
guide is a block guide of a level (`06-geometry.tex`, lines 82–133 and 653–667). This file fixes
the main frame along the schedule:

* `resizedCorners i j`, `repaintedBlocks i j` : the grid corners of scale `j` whose holes have been
  resized, and the blocks of level `j` that have been repainted, by the first `i` events;
* `eventMain`, `mainState` : the main frame before the event number `i`, by the kind of that
  event: the guide uniform on the blocks of the scale of a resize, with the holes of the corners
  already resized of radius `h_n` and the others of radius `h_{2n}`, or the guide of the level of a
  repainting with the blocks already repainted, with holes of radius `h_n`; after the last event,
  the guide of the unit squares.

The auxiliary frames and whole memory are defined in `DyadicProtocolFromEvents`.

The holes of a block guide sit at grid corners of the closed root square
(`exists_index_of_isTrueVertex_levelGuide`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the hierarchy and the
  guides (lines 60–100), the holes and their resizes (lines 102–133), and the memory of the
  protocol (lines 653–667).
-/

noncomputable section

open Set Metric

namespace TNLean.PEPS.Approximation

open EncodedFrame

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

/-- Splitting off event `i` from the first `i + 1` events of the schedule. -/
theorem take_succ_eventSchedule {i : ℕ} (hi : i < (eventSchedule k).length) :
    (eventSchedule k).take (i + 1) = (eventSchedule k).take i ++ [(eventSchedule k)[i]] := by
  exact (List.take_concat_get' _ _ hi).symm

/-- When event `i` resizes junction `J`, its corner is inserted among the resized corners
of that scale. -/
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

/-- When event `i` repaints square `S`, its block is inserted among the repainted blocks
of that level. -/
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

variable {L q : ℕ} {Ω : StateSpace L q} {B₀ C c : ℝ}
  (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
  (R₀ : RepaintedSquare k)

/-- Repainting every block of the root square gives the guide of the end of the level, whatever
the set of repainted blocks outside the root square. -/
theorem levelGuide_eq_univ {j : ℕ} {done : Set (ℤ × ℤ)}
    (hd : {Q | InRoot ((2 : ℤ) ^ (k - j)) Q} ⊆ done) :
    levelGuide k j done = levelGuide k j univ := by
  classical
  have : protocolLevelLabels k j done = protocolLevelLabels k j univ := by
    funext Q
    by_cases hQ : InRoot ((2 : ℤ) ^ (k - j)) Q
    · simp only [protocolLevelLabels, levelLabels, hQ, hd hQ, mem_univ, ite_true]
    · simp only [protocolLevelLabels, levelLabels, hQ, ite_false]
  rw [levelGuide, levelGuide, this]

/-- **From one level to the next.** The guide at the end of the pass to level `2 ^ (j + 1)` is the
guide at the start of the pass to level `2 ^ j`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–86. -/
theorem levelGuide_succ_univ {j : ℕ} (hj : j < k) :
    levelGuide k (j + 1) univ = levelGuide k j ∅ := by
  have h := blockGuide_levelLabels_start (M := (2 : ℤ) ^ (k - (j + 1))) ((2 : ℝ) ^ j)
    (oldParty Sum.inl (j + 1)) (newParty Sum.inl j) (ph := guidePlaceholder)
    (new := newParty Sum.inl (j + 1)) (done := univ) (subset_univ _)
  have h2 : (2 : ℝ) * 2 ^ j = 2 ^ (j + 1) := by ring
  have hM : (2 : ℤ) * 2 ^ (k - (j + 1)) = 2 ^ (k - j) := by
    rw [← pow_succ']; congr 1; omega
  rw [h2, hM] at h
  rw [levelGuide, levelGuide]
  exact congrArg sampleGuide h

/-! ### The main frame before each event -/

section States

variable {ε₀ t : ℝ} (hε : 0 < ε₀) (ht : 0 < t) (hB : ε₀ * t ≤ B₀ * Real.log L)

include hε ht hB in
/-- Under the stated positivity and size bounds, the hole radius lies in its admissible interval. -/
theorem holeRadius_mem {n : ℝ} (hn : 0 < n) :
    0 < holeRadius ε₀ n t ∧ holeRadius ε₀ n t ≤ B₀ * Real.log L :=
  ⟨holeRadius_pos hε hn ht, (holeRadius_le_mul_right hε.le).trans hB⟩

include hε ht hB in
/-- Both resized and unresized hole radii lie in the same admissible interval. -/
theorem resizeRadius_mem {n : ℝ} (hn : 0 < n) (A : Set (ℝ × ℝ)) (z : ℝ × ℝ) :
    0 < resizeRadius ε₀ t n A z ∧ resizeRadius ε₀ t n A z ≤ B₀ * Real.log L := by
  classical
  unfold resizeRadius
  split_ifs
  · exact holeRadius_mem hε ht hB hn
  · exact holeRadius_mem hε ht hB (by positivity)

/-- **The main frame before an event.** Before the event number `i`, if it is the resize at the
junction `J`, the main frame of the guide uniform on the blocks of the scale of `J`, with the
corners resized by the earlier resizes of that scale of radius `h_n` and the others of radius
`h_{2n}`; if it is the repainting of the square `S`, the main frame of the level of `S` with the
blocks repainted by the earlier repaintings of that level, with holes of radius `h_n`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–133. -/
def eventMain (i : ℕ) : ProtocolEvent k → Frame (cellCenterPos L) q (ProtocolParty k)
  | .inr J => levelFrame P rank R₀ J.1 univ
      (resizeRadius ε₀ t ((2 : ℝ) ^ ((J.1 : ℕ) - 1)) (resizedCorners k i J.1))
      (resizeRadius_mem hε ht hB (by positivity) _)
  | .inl S => levelFrame P rank R₀ S.1 (repaintedBlocks k i S.1)
      (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (S.1 : ℕ)) t)
      (fun _ => holeRadius_mem hε ht hB (by positivity))

/-- The main frame after the last event: the guide of the unit squares, with holes of radius
`h_1`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 669–672. -/
def finalMain : Frame (cellCenterPos L) q (ProtocolParty k) :=
  levelFrame P rank R₀ 0 univ (fun _ => holeRadius ε₀ 1 t)
    (fun _ => holeRadius_mem hε ht hB one_pos)

/-- **The main frame between events.** The main frame before the event number `i` of the
schedule, and after the last event the guide of the unit squares.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–133 and 669–672. -/
def mainState (i : ℕ) : Frame (cellCenterPos L) q (ProtocolParty k) :=
  if h : i < (eventSchedule k).length then
    eventMain P rank R₀ hε ht hB i ((eventSchedule k)[i])
  else finalMain P rank R₀ hε ht hB

/-- Before the end of the schedule, the main state is the frame for the current event. -/
theorem mainState_of_lt {i : ℕ} (hi : i < (eventSchedule k).length) :
    mainState P rank R₀ hε ht hB i = eventMain P rank R₀ hε ht hB i ((eventSchedule k)[i]) :=
  dite_eq_left hi

/-- At or after the end of the schedule, the main state is the final frame. -/
theorem mainState_of_le {i : ℕ} (hi : (eventSchedule k).length ≤ i) :
    mainState (q := q) P rank R₀ hε ht hB i = finalMain P rank R₀ hε ht hB :=
  dite_eq_right (not_lt.2 hi)

end States

end TNLean.PEPS.Approximation
