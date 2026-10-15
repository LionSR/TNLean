/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolBoundaryStates

/-!
# The main frame from one event to the next

Each event of the schedule of Proposition 7.1 of the polynomial-PEPS manuscript passes the main
frame from the frame before it to the frame before the next event (`06-geometry.tex`, lines
82–133): a resize enlarges the set of resized corners by its own corner, and a repainting the set
of repainted blocks by its own block. When the next event belongs to the next phase, the frames
describe the same guide: after the last resize of a scale every hole has the radius of the next
level and the guide uniform on the blocks of that scale is the guide at the start of the next
level (`eventMain_inr_succ`); after the last repainting of a level the guide is the guide uniform
on its blocks (`eventMain_inl_succ`). Before the first event the main frame is the raw copy at
the root party (`mainState_zero`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the repainting by levels
  (lines 82–100), the resizes (lines 127–131), and the initial copy (lines 658–661).
-/

noncomputable section

open Set Metric

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k : ℕ}

/-! ### Events of the schedule -/

/-- The square of level `j < k` with block indices `Q` in the root square. -/
def squareOfIndex {j : ℕ} (hj : j < k) {Q : ℤ × ℤ} (hQ : InRoot ((2 : ℤ) ^ (k - j)) Q) :
    DyadicSquare k :=
  ⟨⟨j, by omega⟩, ⟨Q.1.toNat, by
    show Q.1.toNat < 2 ^ (k - j)
    obtain ⟨h1, h2, -, -⟩ := hQ
    have : ((2 ^ (k - j) : ℕ) : ℤ) = (2 : ℤ) ^ (k - j) := by push_cast; rfl
    omega⟩, ⟨Q.2.toNat, by
    show Q.2.toNat < 2 ^ (k - j)
    obtain ⟨-, -, h3, h4⟩ := hQ
    have : ((2 ^ (k - j) : ℕ) : ℤ) = (2 : ℤ) ^ (k - j) := by push_cast; rfl
    omega⟩⟩

theorem squareOfIndex_index {j : ℕ} (hj : j < k) {Q : ℤ × ℤ}
    (hQ : InRoot ((2 : ℤ) ^ (k - j)) Q) : (squareOfIndex hj hQ).index = Q := by
  obtain ⟨h1, -, h3, -⟩ := hQ
  simp only [squareOfIndex, DyadicSquare.index]
  ext <;> simp <;> omega

/-- The junction of scale `j ≤ k` at the grid corner with indices `Q` in the closed root square. -/
def junctionOfIndex {j : ℕ} (hj : j ≤ k) {Q : ℤ × ℤ} (h1 : 0 ≤ Q.1) (h2 : Q.1 ≤ 2 ^ (k - j))
    (h3 : 0 ≤ Q.2) (h4 : Q.2 ≤ 2 ^ (k - j)) : DyadicJunction k :=
  ⟨⟨j, by omega⟩, ⟨Q.1.toNat, by
    show Q.1.toNat < 2 ^ (k - j) + 1
    have : ((2 ^ (k - j) : ℕ) : ℤ) = (2 : ℤ) ^ (k - j) := by push_cast; rfl
    omega⟩, ⟨Q.2.toNat, by
    show Q.2.toNat < 2 ^ (k - j) + 1
    have : ((2 ^ (k - j) : ℕ) : ℤ) = (2 : ℤ) ^ (k - j) := by push_cast; rfl
    omega⟩⟩

theorem junctionOfIndex_index {j : ℕ} (hj : j ≤ k) {Q : ℤ × ℤ} (h1 : 0 ≤ Q.1)
    (h2 : Q.1 ≤ 2 ^ (k - j)) (h3 : 0 ≤ Q.2) (h4 : Q.2 ≤ 2 ^ (k - j)) :
    (junctionOfIndex hj h1 h2 h3 h4).index = Q := by
  simp only [junctionOfIndex, DyadicJunction.index]
  ext <;> simp <;> omega

/-- The events of the schedule are distinct, and the event number `i` is not among the first `i`.
-/
theorem getElem_notMem_take {i : ℕ} (hi : i < (eventSchedule k).length) :
    (eventSchedule k)[i] ∉ (eventSchedule k).take i := by
  intro h
  obtain ⟨m, hm, he⟩ := List.mem_take_iff_getElem.1 h
  have := (List.Nodup.getElem_inj_iff (nodup_eventSchedule k)).1 he
  omega

/-- A scheduled event of the rank of an event later than the event number `i` is not among the
first `i + 1` events. -/
theorem notMem_take_succ_of_rank {i : ℕ} (hi : i + 1 < (eventSchedule k).length)
    {e : ProtocolEvent k} (hr : ((eventSchedule k)[i]).rank < e.rank) :
    e ∉ (eventSchedule k).take (i + 1) := by
  intro h
  obtain ⟨m, hm, rfl⟩ := List.mem_take_iff_getElem.1 h
  have := rank_getElem_le_of_le (k := k) (i := m) (j := i) (by omega) (by omega)
  omega

/-- The last event has the largest rank `2 k + 1`. -/
theorem rank_getElem_last (hk : 1 ≤ k) {i : ℕ} (hi : i + 1 = (eventSchedule k).length) :
    ((eventSchedule k)[i]'(by omega)).rank = 2 * k + 1 := by
  obtain ⟨e, he, her⟩ := exists_isScheduled_rank (k := k) (r := 2 * k + 1) (by omega) le_rfl
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 (mem_eventSchedule.2 he)
  have := rank_getElem_le_of_le (k := k) (i := m) (j := i) (by omega) (by omega)
  have := ProtocolEvent.rank_le ((eventSchedule k)[i]'(by omega))
  omega

/-- The first event has the smallest rank `2`. -/
theorem rank_getElem_zero (hk : 1 ≤ k) (h0 : 0 < (eventSchedule k).length) :
    ((eventSchedule k)[0]).rank = 2 := by
  obtain ⟨e, he, her⟩ := exists_isScheduled_rank (k := k) (r := 2) le_rfl (by omega)
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 (mem_eventSchedule.2 he)
  have := rank_getElem_le_of_le (k := k) (i := 0) (j := m) (Nat.zero_le _) hm
  have := ProtocolEvent.two_le_rank (isScheduled_getElem h0)
  omega

/-- The schedule is not empty when `k ≥ 1`. -/
theorem length_eventSchedule_pos (hk : 1 ≤ k) : 0 < (eventSchedule k).length := by
  obtain ⟨e, he, -⟩ := exists_isScheduled_rank (k := k) (r := 2) le_rfl (by omega)
  exact List.length_pos_of_mem (mem_eventSchedule.2 he)

/-! ### The transitions -/

section Transitions

variable {L q : ℕ} {Ω : StateSpace L q} {B₀ C c : ℝ}
  (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
  (R₀ : RepaintedSquare k) {ε₀ t : ℝ} (hε : 0 < ε₀) (ht : 0 < t)
  (hB : ε₀ * t ≤ B₀ * Real.log L)

/-- **After a resize.** The resize at the junction `J`, the event number `i`, leaves the main frame
of the guide uniform on the blocks of the scale of `J` with the corner of `J` resized as well: the
main frame before the next event, or a frame equal to it when the next event starts the next
level.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–87 and 127–131. -/
theorem eventMain_inr_succ (hk : 1 ≤ k) {i : ℕ} (hi : i < (eventSchedule k).length)
    {J : DyadicJunction k} (he : (eventSchedule k)[i] = .inr J) :
    levelFrame P rank R₀ J.1 univ
        (resizeRadius ε₀ t ((2 : ℝ) ^ ((J.1 : ℕ) - 1))
          (insert (blockCorner ((2 : ℝ) ^ (J.1 : ℕ)) J.index) (resizedCorners k i J.1)))
        (resizeRadius_mem hε ht hB (by positivity) _) =
      mainState (q := q) P rank R₀ hε ht hB (i + 1) := by
  have hJ0 : 0 < (J.1 : ℕ) := by
    have := isScheduled_getElem hi; rw [he] at this; exact this
  have hJk := Nat.lt_succ_iff.1 J.1.isLt
  have hrJ : ((eventSchedule k)[i]).rank = 2 * (k - ((J.1 : ℕ) - 1)) := by
    rw [he, ProtocolEvent.rank_inr]
  rw [← resizedCorners_succ_inr hi he]
  rcases Nat.lt_or_ge (i + 1) (eventSchedule k).length with hi1 | hi1
  · rw [mainState_of_lt _ _ _ _ _ _ hi1]
    have hr1 := rank_getElem_succ_le hi1
    have hr2 := rank_getElem_le_of_le (k := k) (Nat.le_succ i) hi1
    rcases he' : (eventSchedule k)[i + 1] with S' | J'
    · -- the next event repaints the first square of the next level
      have hS := isScheduled_getElem hi1
      rw [he'] at hr1 hr2 hS
      change (S'.1 : ℕ) < k at hS
      rw [ProtocolEvent.rank_inl, hrJ] at hr1 hr2
      have hSJ : (S'.1 : ℕ) = (J.1 : ℕ) - 1 := by omega
      have hempty : repaintedBlocks k (i + 1) S'.1 = ∅ := by
        refine eq_empty_of_forall_notMem fun Q ⟨S'', hS'', hj, _⟩ => ?_
        refine notMem_take_succ_of_rank hi1 (e := .inl S'') ?_ hS''
        rw [hrJ, ProtocolEvent.rank_inl, hj]
        omega
      simp only [eventMain]
      refine levelFrame_eq_of_levelGuide_eq P rank R₀ _ _ ?_ fun z hz => ?_
      · rw [hempty, hSJ, ← levelGuide_succ_univ (by omega), Nat.sub_add_cancel hJ0]
      · obtain ⟨Q, rfl, h1, h2, h3, h4⟩ :=
          exists_index_of_isTrueVertex_levelGuide (mem_levelVertices.1 hz)
        have hmem : blockCorner ((2 : ℝ) ^ (J.1 : ℕ)) Q ∈ resizedCorners k (i + 1) J.1 := by
          refine ⟨junctionOfIndex hJk h1 h2 h3 h4, ?_, rfl,
            by rw [junctionOfIndex_index]⟩
          refine mem_take_of_rank_lt hi1 (by change 0 < (J.1 : ℕ); exact hJ0) ?_
          rw [he', ProtocolEvent.rank_inl, ProtocolEvent.rank_inr]
          change 2 * (k - ((J.1 : ℕ) - 1)) < _
          omega
        classical
        simp only [resizeRadius, hmem, ite_true, hSJ]
    · -- the next event resizes another corner of the same scale
      have hJ' := isScheduled_getElem hi1
      rw [he'] at hr1 hr2 hJ'
      change 0 < (J'.1 : ℕ) at hJ'
      have hJ'k := Nat.lt_succ_iff.1 J'.1.isLt
      rw [ProtocolEvent.rank_inr, hrJ] at hr1 hr2
      have hJJ : (J'.1 : ℕ) = J.1 := by omega
      simp only [eventMain]
      refine levelFrame_eq_of_levelGuide_eq P rank R₀ _ _ (by rw [hJJ]) fun z _ => ?_
      rw [hJJ]
  · -- the last event is a repainting, not a resize
    exfalso
    have := rank_getElem_last hk (i := i) (by omega)
    rw [hrJ] at this
    omega

/-- After the repainting of the square `S`, the event number `i`, every block of the root square of
its level is repainted when the next event has a larger rank or there is no next event. -/
theorem inRoot_subset_repaintedBlocks {i : ℕ} (hi : i < (eventSchedule k).length)
    {S : DyadicSquare k} (he : (eventSchedule k)[i] = .inl S)
    (hnext : ∀ hi1 : i + 1 < (eventSchedule k).length,
      ((eventSchedule k)[i]).rank < ((eventSchedule k)[i + 1]).rank) :
    {Q | InRoot ((2 : ℤ) ^ (k - (S.1 : ℕ))) Q} ⊆ repaintedBlocks k (i + 1) S.1 := by
  intro Q hQ
  have hS : (S.1 : ℕ) < k := by
    have := isScheduled_getElem hi; rw [he] at this; exact this
  refine ⟨squareOfIndex hS hQ, ?_, rfl, (squareOfIndex_index hS hQ).symm⟩
  have hsch : ProtocolEvent.IsScheduled (Sum.inl (squareOfIndex hS hQ) : ProtocolEvent k) := by
    change (S.1 : ℕ) < k; exact hS
  rcases Nat.lt_or_ge (i + 1) (eventSchedule k).length with hi1 | hi1
  · refine mem_take_of_rank_lt hi1 hsch ?_
    have h := hnext hi1
    rw [he] at h
    rw [ProtocolEvent.rank_inl] at h ⊢
    exact h
  · rw [List.take_of_length_le hi1]
    exact mem_eventSchedule.2 hsch

/-- **After a repainting.** The repainting of the square `S`, the event number `i`, leaves the
main frame of its level with `S` repainted as well: the main frame before the next event, or a
frame equal to it when the next event resizes the corners entering the next level, or the main
frame of the unit squares after the last event.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–90, 127–131 and 669–672. -/
theorem eventMain_inl_succ (hk : 1 ≤ k) {i : ℕ} (hi : i < (eventSchedule k).length)
    {S : DyadicSquare k} (he : (eventSchedule k)[i] = .inl S) :
    levelFrame P rank R₀ S.1 (insert S.index (repaintedBlocks k i S.1))
        (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (S.1 : ℕ)) t)
        (fun _ => holeRadius_mem hε ht hB (by positivity)) =
      mainState (q := q) P rank R₀ hε ht hB (i + 1) := by
  have hS : (S.1 : ℕ) < k := by
    have := isScheduled_getElem hi; rw [he] at this; exact this
  have hrS : ((eventSchedule k)[i]).rank = 2 * (k - (S.1 : ℕ)) + 1 := by
    rw [he, ProtocolEvent.rank_inl]
  rw [← repaintedBlocks_succ_inl hi he]
  rcases Nat.lt_or_ge (i + 1) (eventSchedule k).length with hi1 | hi1
  · rw [mainState_of_lt _ _ _ _ _ _ hi1]
    have hr1 := rank_getElem_succ_le hi1
    have hr2 := rank_getElem_le_of_le (k := k) (Nat.le_succ i) hi1
    rcases he' : (eventSchedule k)[i + 1] with S' | J'
    · -- the next event repaints another square of the same level
      rw [he', ProtocolEvent.rank_inl, hrS] at hr1 hr2
      have hSS : (S'.1 : ℕ) = S.1 := by have := S'.1.isLt; omega
      simp only [eventMain]
      refine levelFrame_eq_of_levelGuide_eq P rank R₀ _ _ (by rw [hSS]) fun z _ => ?_
      rw [hSS]
    · -- the next event resizes the corners entering the next level
      have hJ' := isScheduled_getElem hi1
      rw [he'] at hr1 hr2 hJ'
      change 0 < (J'.1 : ℕ) at hJ'
      have hJ'k := Nat.lt_succ_iff.1 J'.1.isLt
      rw [ProtocolEvent.rank_inr, hrS] at hr1 hr2
      have hJS : (J'.1 : ℕ) = S.1 := by omega
      have hall := inRoot_subset_repaintedBlocks hi he fun h => by
        rw [he', hrS, ProtocolEvent.rank_inr]; omega
      have hempty : resizedCorners k (i + 1) J'.1 = ∅ := by
        refine eq_empty_of_forall_notMem fun z ⟨J'', hJ'', hj, _⟩ => ?_
        refine notMem_take_succ_of_rank hi1 (e := .inr J'') ?_ hJ''
        rw [hrS, ProtocolEvent.rank_inr, hj]
        omega
      simp only [eventMain]
      refine levelFrame_eq_of_levelGuide_eq P rank R₀ _ _ ?_ fun z _ => ?_
      · rw [levelGuide_eq_univ hall, hJS]
      · classical
        rw [hempty]
        simp only [resizeRadius, mem_empty_iff_false, ite_false, hJS]
        congr 1
        rw [← pow_succ']
        congr 1
        omega
  · -- the last event repaints a unit square
    rw [mainState_of_le _ _ _ _ _ _ hi1]
    have hlast := rank_getElem_last hk (i := i) (by omega)
    rw [hrS] at hlast
    have hS0 : (S.1 : ℕ) = 0 := by omega
    have hall := inRoot_subset_repaintedBlocks hi he fun h => by omega
    refine levelFrame_eq_of_levelGuide_eq P rank R₀ _ _ ?_ fun z _ => ?_
    · rw [levelGuide_eq_univ hall, hS0]
    · simp only [hS0, pow_zero]

/-! ### The first and the last main frames -/

/-- Two frames with the same owners and the same holes are equal. -/
theorem frame_eq_of_owner_holes {ι Party : Type*} [Fintype ι] [DecidableEq ι] {q' : ℕ}
    {pos : ι → ℝ × ℝ} {F G : Frame pos q' Party} (h₁ : F.owner = G.owner)
    (h₂ : F.holes = G.holes) : F = G := by
  cases F; cases G
  simp only at h₁ h₂
  subst h₁ h₂
  rfl

/-- **The label read at a site.** If a block guide of a level is constant on the open set `U`
around a point, its sampled guide takes that value at the point. -/
theorem levelGuide_eq_of_mem_open {j : ℕ} {done : Set (ℤ × ℤ)} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {p : ℝ × ℝ} (hp : p ∈ U) {l : GuideLabel}
    (hl : ∀ x ∈ U, blockGuide ((2 : ℝ) ^ j) (protocolLevelLabels k j done) x = l) :
    levelGuide k j done p = l := by
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), p + ε • ((1 : ℝ), (1 : ℝ)) ∈ U :=
    tendsto_add_smul_nhdsGT p _ (hU.mem_nhds hp)
  obtain ⟨ε, he, hmem⟩ := (((isDisplacedReading_levelGuide (k := k) j done) p).and hev).exists
  rw [he]
  exact hl _ hmem

/-- **The first main frame.** Before the first event the main guide carries the root label inside
the root square, so the main frame is the raw copy held by the party of the root square.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 21–23 and 658–661. -/
theorem mainState_zero (hk : 1 ≤ k) (hkL : L ≤ 2 ^ k) :
    mainState (q := q) P rank R₀ hε ht hB 0 = Frame.raw fun _ => .inl (rootSquare k) := by
  have h0 := length_eventSchedule_pos hk
  have hr := rank_getElem_zero hk h0
  rw [mainState_of_lt _ _ _ _ _ _ h0]
  rcases he : (eventSchedule k)[0] with S | J
  · rw [he, ProtocolEvent.rank_inl] at hr; omega
  · have hJ0 : 0 < (J.1 : ℕ) := by
      have := isScheduled_getElem h0; rw [he] at this; exact this
    rw [he, ProtocolEvent.rank_inr] at hr
    have hJk := Nat.lt_succ_iff.1 J.1.isLt
    have hJ : (J.1 : ℕ) = k := by omega
    simp only [eventMain]
    have hV : levelVertices k J.1 univ = ∅ := by rw [hJ]; exact levelVertices_self univ
    have hd : ((levelVertices k J.1 univ : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise fun z z' =>
        Disjoint (suppliedPatch P (resizeRadius ε₀ t ((2 : ℝ) ^ ((J.1 : ℕ) - 1))
          (resizedCorners k 0 J.1)) (resizeRadius_mem hε ht hB (by positivity) _) z).outer
          (suppliedPatch P (resizeRadius ε₀ t ((2 : ℝ) ^ ((J.1 : ℕ) - 1))
            (resizedCorners k 0 J.1)) (resizeRadius_mem hε ht hB (by positivity) _) z').outer := by
      rw [hV]; simp
    rw [levelFrame_eq P rank R₀ hd]
    refine frame_eq_of_owner_holes (funext fun x => ?_) ?_
    · simp only [guideFrame_owner]
      have hroot : (rootSquare k).toTriple = (k, 0, 0) := rfl
      have hl : ∀ y ∈ openRoot k, blockGuide ((2 : ℝ) ^ (J.1 : ℕ))
          (protocolLevelLabels k J.1 univ) y = .inl (rootSquare k).toTriple := by
        classical
        intro y hy
        obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hy
        have hb : blockIndex ((2 : ℝ) ^ (J.1 : ℕ)) y = (0, 0) := by
          simp only [blockIndex, hJ]
          refine Prod.ext (Int.floor_eq_zero_iff.2 ⟨?_, ?_⟩) (Int.floor_eq_zero_iff.2 ⟨?_, ?_⟩)
          · positivity
          · rw [div_lt_one (by positivity)]; exact a2
          · positivity
          · rw [div_lt_one (by positivity)]; exact a4
        have hin : InRoot ((2 : ℤ) ^ (k - (J.1 : ℕ))) (0, 0) := by
          rw [hJ, Nat.sub_self, pow_zero]; exact ⟨le_rfl, one_pos, le_rfl, one_pos⟩
        simp only [hJ] at hb hin ⊢
        simp only [blockGuide, hb, protocolLevelLabels, levelLabels, hin, mem_univ, ite_true,
          newParty, hroot]
        rfl
      rw [levelGuide_eq_of_mem_open (isOpen_Ioo.prod isOpen_Ioo)
        (cellCenterPos_mem_openRoot hkL x) hl, labelParty_toTriple]
      rfl
    · simp only [guideFrame, hV, Finset.toList_empty, List.map_nil]
      rfl

end Transitions

end TNLean.PEPS.Approximation
