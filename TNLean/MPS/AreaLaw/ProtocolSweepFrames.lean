/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic
import TNLean.MPS.AreaLaw.ProtocolTerminalCoordinates
import TNLean.MPS.AreaLaw.ProtocolSweepGeometry
import TNLean.MPS.AreaLaw.BandDissolution
import TNLean.PEPS.Approximation.HomogeneousOwnership

/-!
# The main-sheet frames of successive chain stages

The main sheet is described by the existing hole-free frame. The two births
and the endpoints of the two band transfers are explicit changes of owner.
The ownership calculations identify the next stage, the actual environments
of both births, and the flanks required for both band operations. The corrected
one-band construction supplies the actual main frames with these endpoints.
At stage zero the left transfer is a direct death; there is no fictitious
left-hand party.

These are intermediate ownership statements, not constructions of the gates
or their information estimates. Source: the one-dimensional note, Part II,
`part2b_mps_protocol.tex`, Construction `con:sweep`, lines 330–343, and the
proof of Proposition `prop:sweep`, lines 365–378.

**Local fix (half-open lattice bands):** Integer-ended bands are half-open;
the unchanged open exchange window belongs to the separate band construction.
The correction is recorded in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.PEPS.EncodedFrame

variable {L w q : ℕ} {pos : Fin L → ℝ × ℝ}

/-- Before stage `k`, completed blocks retain their respective parties and the
suffix belongs to the remainder party `R_k`.
Source: Part II, `con:sweep`, lines 331–332. -/
def stageOwner (L w : ℕ) (k : Fin (stageCount L w + 1)) (x : Fin L) : Party L w :=
  if hx : x.val < k.val * (20 * w) then
    .inr ⟨x.val / (20 * w), Nat.lt_of_lt_of_le
      (Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hx))
      (Nat.le_of_lt_succ k.isLt)⟩
  else .inl k

/-- The actual hole-free main-sheet frame before a stage.
Source: Part II, `con:sweep`, lines 331–332. -/
def stageFrame (L w q : ℕ) (pos : Fin L → ℝ × ℝ)
    (k : Fin (stageCount L w + 1)) : Frame pos q (Party L w) :=
  Frame.raw (stageOwner L w k)

/-- The first birth gives the far suffix to the next remainder party.
Source: Part II, `con:sweep`, move (1), line 334. -/
def remainderBirthTarget (L w : ℕ) (k : Fin (stageCount L w)) : Finset (Fin L) :=
  interval L ((k.val + 1) * (20 * w) + w) L

/-- The second birth gives the interior of the next block to its new owner.
Source: Part II, `con:sweep`, move (2), line 335. -/
def blockBirthTarget (L w : ℕ) (k : Fin (stageCount L w)) : Finset (Fin L) :=
  interval L (k.val * (20 * w) + w) ((k.val + 1) * (20 * w))

/-- The left band at stage `k`, including stage zero's direct death.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
def leftBandTarget (L w : ℕ) (k : Fin (stageCount L w)) : Finset (Fin L) :=
  interval L (k.val * (20 * w)) (k.val * (20 * w) + w)

/-- The right band at stage `k`.
Source: Part II, `con:sweep`, move (4), lines 339–340. -/
def rightBandTarget (L w : ℕ) (k : Fin (stageCount L w)) : Finset (Fin L) :=
  interval L ((k.val + 1) * (20 * w)) ((k.val + 1) * (20 * w) + w)

/-- The frame after the first actual birth target changes owner.
Source: Part II, `con:sweep`, move (1), line 334. -/
def afterRemainderBirth (L w q : ℕ) (pos : Fin L → ℝ × ℝ)
    (k : Fin (stageCount L w)) : Frame pos q (Party L w) :=
  (stageFrame L w q pos k.castSucc).changeOwner (remainderBirthTarget L w k) (.inl k.succ)

/-- The frame after both actual birth targets change owner.
Source: Part II, `con:sweep`, moves (1)–(2), lines 333–334. -/
def afterBlockBirth (L w q : ℕ) (pos : Fin L → ℝ × ℝ)
    (k : Fin (stageCount L w)) : Frame pos q (Party L w) :=
  (afterRemainderBirth L w q pos k).changeOwner (blockBirthTarget L w k) (.inr k)

/-- The main-sheet endpoint of the left band transfer. At stage zero the same
endpoint is obtained by a direct death. Realizing this change is separate.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
def afterLeftTransfer (L w q : ℕ) (pos : Fin L → ℝ × ℝ)
    (k : Fin (stageCount L w)) : Frame pos q (Party L w) :=
  (afterBlockBirth L w q pos k).changeOwner (leftBandTarget L w k) (.inr k)

/-- The main-sheet endpoint of the right band transfer. Realization by the
corrected band construction is a separate obligation.
Source: Part II, `con:sweep`, move (4), lines 339–340. -/
def afterRightTransfer (L w q : ℕ) (pos : Fin L → ℝ × ℝ)
    (k : Fin (stageCount L w)) : Frame pos q (Party L w) :=
  (afterLeftTransfer L w q pos k).changeOwner (rightBandTarget L w k) (.inl k.succ)

/-- A site in the kth half-open block has quotient k.
Source: Part II, `eq:blocks`, lines 247–255. -/
private theorem div_eq_of_mem_block (hw : 1 ≤ w) {x k : ℕ}
    (hlo : k * (20 * w) ≤ x) (hhi : x < (k + 1) * (20 * w)) :
    x / (20 * w) = k := by
  have ht : 0 < 20 * w := by omega
  have h₁ : k ≤ x / (20 * w) := (Nat.le_div_iff_mul_le ht).2 hlo
  have h₂ : x / (20 * w) < k + 1 := (Nat.div_lt_iff_lt_mul ht).2 hhi
  omega

/-- A frame with no holes is the raw frame of its actual owner. -/
private theorem raw_owner_eq (F : Frame pos q (Party L w)) (hF : F.holes = []) :
    Frame.raw F.owner = F := by
  cases F with
  | mk owner holes disjoint => cases hF; rfl

/-- A completed block keeps its actual finite party label at a later stage.
Source: Part II, `con:sweep`, lines 331–332. -/
private theorem stageOwner_at_block (hw : 1 ≤ w)
    (k : Fin (stageCount L w + 1)) (j : Fin (stageCount L w)) (x : Fin L)
    (hjk : j.val < k.val) (hlo : j.val * (20 * w) ≤ x.val)
    (hhi : x.val < (j.val + 1) * (20 * w)) : stageOwner L w k x = Sum.inr j := by
  have hmul := Nat.mul_le_mul_right (20 * w) (show j.val + 1 ≤ k.val by omega)
  have hx : x.val < k.val * (20 * w) := hhi.trans_le hmul
  have hdiv := div_eq_of_mem_block hw hlo hhi
  unfold stageOwner
  rw [dite_eq_left hx]
  exact congrArg Sum.inr (Fin.ext hdiv)

/-- Neither birth changes a site before the new block interior.
Source: Part II, `con:sweep`, moves (1)–(2), lines 334–335. -/
private theorem unused_births_of_lt (k : Fin (stageCount L w)) (x : Fin L)
    (hx : x.val < k.val * (20 * w) + w) :
    x ∉ remainderBirthTarget L w k ∧ x ∉ blockBirthTarget L w k := by
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  simp only [remainderBirthTarget, blockBirthTarget, mem_interval]
  omega

/-- The completed-block birth and left transfer do not change a site in
the next remainder. Source: Part II, `con:sweep`, moves (2)–(3), lines 335–338. -/
private theorem passed_targets_of_le (k : Fin (stageCount L w)) (x : Fin L)
    (hx : (k.val + 1) * (20 * w) ≤ x.val) :
    x ∉ blockBirthTarget L w k ∧ x ∉ leftBandTarget L w k := by
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  simp only [blockBirthTarget, leftBandTarget, mem_interval]
  omega

/-- Initially the entire main sheet belongs to `R_0`.
Source: Part II, `con:sweep`, line 331. -/
theorem stageOwner_zero (L w : ℕ) :
    stageOwner L w 0 = fun _ ↦ Sum.inl (0 : Fin (stageCount L w + 1)) := by
  funext x
  simp [stageOwner]

/-- The final stage has exactly the previously specified terminal main owner.
Source: Part II, `con:sweep`, line 342. -/
theorem stageOwner_last (L w : ℕ) :
    stageOwner L w (Fin.last (stageCount L w)) = mainOwner L w := by
  rfl

/-- Both birth targets are actually held by `R_k` immediately before their
respective births. Source: Part II, `prop:sweep`, proof, lines 365–369. -/
theorem birth_targets_owned (hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    (∀ x ∈ remainderBirthTarget L w k,
      (stageFrame L w q pos k.castSucc).owner x = Sum.inl k.castSucc) ∧
    (∀ x ∈ blockBirthTarget L w k,
      (afterRemainderBirth L w q pos k).owner x = Sum.inl k.castSucc) := by
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  constructor
  · intro x hx
    have hx' : (k.val + 1) * (20 * w) + w ≤ x.val ∧ x.val < L := by
      simpa only [remainderBirthTarget, mem_interval] using hx
    have hpre : ¬x.val < k.val * (20 * w) := by omega
    simp [stageFrame, Frame.raw, stageOwner, hpre]
  · intro x hx
    have hx' : k.val * (20 * w) + w ≤ x.val ∧
        x.val < (k.val + 1) * (20 * w) := by
      simpa only [blockBirthTarget, mem_interval] using hx
    have hpre : ¬x.val < k.val * (20 * w) := by omega
    have hR : x ∉ remainderBirthTarget L w k := by
      simp only [remainderBirthTarget, mem_interval]
      omega
    simp [afterRemainderBirth, Frame.changeOwner, stageFrame, Frame.raw, stageOwner, hR, hpre]

/-- The environments are computed from the actual before-birth frames, rather
than supplied as hypotheses. Source: Part II, `prop:sweep`, lines 365–369. -/
theorem birth_environments (_hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    (stageFrame L w q pos k.castSucc).birthEnv (.inl k.castSucc) =
        interval L 0 (k.val * (20 * w)) ∧
      (afterRemainderBirth L w q pos k).birthEnv (.inl k.castSucc) =
        interval L 0 (k.val * (20 * w)) ∪ remainderBirthTarget L w k := by
  have hne : k.succ ≠ k.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  constructor
  · ext x
    by_cases hx : x.val < k.val * (20 * w)
    · simp [Frame.birthEnv, stageFrame, stageOwner, Frame.outerHoles,
        Frame.patches, Frame.raw, footprint, mem_interval, hx]
    · simp [Frame.birthEnv, stageFrame, stageOwner, Frame.outerHoles,
        Frame.patches, Frame.raw, footprint, mem_interval, hx]
  · ext x
    by_cases hx : x.val < k.val * (20 * w) <;>
      by_cases hR : x ∈ remainderBirthTarget L w k <;>
      simp [Frame.birthEnv, afterRemainderBirth, Frame.changeOwner, stageFrame,
        stageOwner, Frame.outerHoles, Frame.patches, Frame.raw, footprint,
        mem_interval, hx, hR, hne]

/-- At a positive stage the completed block supplies the left flank of the
left band, while the new block supplies its right flank.
Source: Part II, `prop:sweep`, lines 370–374. -/
theorem left_band_owners (hw : 1 ≤ w) (k : Fin (stageCount L w)) (hk : 0 < k.val) :
    let a := k.val * (20 * w)
    (∀ x ∈ interval L (a - 8 * w) a,
      (afterBlockBirth L w q pos k).owner x =
        Sum.inr ⟨k.val - 1, by omega⟩) ∧
      (∀ x ∈ interval L a (a + w),
        (afterBlockBirth L w q pos k).owner x = Sum.inl k.castSucc) ∧
      (∀ x ∈ interval L (a + w) (a + 2 * w),
        (afterBlockBirth L w q pos k).owner x = Sum.inr k) := by
  dsimp only
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  have hp : k.val - 1 + 1 = k.val := by omega
  have hpred := congrArg (fun n : ℕ ↦ n * (20 * w)) hp
  simp only [Nat.add_mul, Nat.one_mul] at hpred
  have hmargin : 8 * w ≤ k.val * (20 * w) := stage_left_margin w k.val (by omega)
  constructor
  · intro x hx
    have hx' : k.val * (20 * w) - 8 * w ≤ x.val ∧
        x.val < k.val * (20 * w) := by simpa only [mem_interval] using hx
    have hlo : (k.val - 1) * (20 * w) ≤ x.val := by omega
    have hhi : x.val < (k.val - 1 + 1) * (20 * w) := by simpa only [hp] using hx'.2
    have howner := stageOwner_at_block (L := L) hw k.castSucc
      (⟨k.val - 1, by omega⟩ : Fin (stageCount L w)) x
      (by change k.val - 1 < k.val; omega) hlo hhi
    obtain ⟨hR, hB⟩ := unused_births_of_lt k x (by omega)
    simpa [afterBlockBirth, afterRemainderBirth, Frame.changeOwner, stageFrame, Frame.raw,
      hR, hB] using howner
  · constructor
    · intro x hx
      have hx' : k.val * (20 * w) ≤ x.val ∧
          x.val < k.val * (20 * w) + w := by simpa only [mem_interval] using hx
      have hpre : ¬x.val < k.val * (20 * w) := by omega
      obtain ⟨hR, hB⟩ := unused_births_of_lt k x (by omega)
      simp [afterBlockBirth, afterRemainderBirth, Frame.changeOwner,
        stageFrame, Frame.raw, stageOwner, hR, hB, hpre]
    · intro x hx
      have hx' : k.val * (20 * w) + w ≤ x.val ∧
          x.val < k.val * (20 * w) + 2 * w := by simpa only [mem_interval] using hx
      have hB : x ∈ blockBirthTarget L w k := by
        simp only [blockBirthTarget, mem_interval]
        omega
      simp [afterBlockBirth, Frame.changeOwner, hB]

/-- The exceptional first left transfer is a direct death whose after-death
environment is the rest of the chain. Source: Part II, `prop:sweep`, lines 373–374. -/
theorem first_left_death_environment (_hw : 1 ≤ w) (k : Fin (stageCount L w))
    (hk : k.val = 0) :
    (afterLeftTransfer L w q pos k).birthEnv (.inr k) = interval L (20 * w) L := by
  ext x
  have houter : x ∉ (afterLeftTransfer L w q pos k).outerHoles := by
    simp [Frame.outerHoles, Frame.patches, afterLeftTransfer, afterBlockBirth,
      afterRemainderBirth, Frame.changeOwner, stageFrame, Frame.raw, footprint]
  have hP : (afterLeftTransfer L w q pos k).owner x = Sum.inr k ↔
      x.val < 20 * w := by
    simp only [afterLeftTransfer, afterBlockBirth, afterRemainderBirth,
      Frame.changeOwner, stageFrame, Frame.raw, stageOwner, leftBandTarget,
      blockBirthTarget, remainderBirthTarget, mem_interval, Fin.val_castSucc, hk,
      zero_mul, zero_add, one_mul, Nat.not_lt_zero, dite_false]
    split_ifs <;> simp_all
    omega
  simp only [Frame.mem_birthEnv, houter, or_false, ne_eq, hP, mem_interval]
  have hxL := x.isLt
  omega

/-- After the left transfer the new completed block supplies the full left
flank of the right band. Source: Part II, `prop:sweep`, lines 374–376. -/
theorem right_band_owners (_hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    let b := (k.val + 1) * (20 * w)
    (∀ x ∈ interval L (b - 8 * w) b,
      (afterLeftTransfer L w q pos k).owner x = Sum.inr k) ∧
      (∀ x ∈ interval L b (b + w),
        (afterLeftTransfer L w q pos k).owner x = Sum.inl k.castSucc) ∧
      (∀ x ∈ interval L (b + w) (b + 2 * w),
        (afterLeftTransfer L w q pos k).owner x = Sum.inl k.succ) := by
  dsimp only
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  constructor
  · intro x hx
    have hx' : (k.val + 1) * (20 * w) - 8 * w ≤ x.val ∧
        x.val < (k.val + 1) * (20 * w) := by simpa only [mem_interval] using hx
    have hB : x ∈ blockBirthTarget L w k := by
      simp only [blockBirthTarget, mem_interval]
      omega
    have hleft : x ∉ leftBandTarget L w k := by
      simp only [leftBandTarget, mem_interval]
      omega
    simp [afterLeftTransfer, afterBlockBirth, Frame.changeOwner, hleft, hB]
  · constructor
    · intro x hx
      have hx' : (k.val + 1) * (20 * w) ≤ x.val ∧
          x.val < (k.val + 1) * (20 * w) + w := by simpa only [mem_interval] using hx
      have hpre : ¬x.val < k.val * (20 * w) := by omega
      have hR : x ∉ remainderBirthTarget L w k := by
        simp only [remainderBirthTarget, mem_interval]
        omega
      obtain ⟨hB, hleft⟩ := passed_targets_of_le k x hx'.1
      simp [afterLeftTransfer, afterBlockBirth, afterRemainderBirth,
        Frame.changeOwner, stageFrame, Frame.raw, stageOwner, hpre, hR, hB, hleft]
    · intro x hx
      have hx' : (k.val + 1) * (20 * w) + w ≤ x.val ∧
          x.val < (k.val + 1) * (20 * w) + 2 * w := by simpa only [mem_interval] using hx
      have hR : x ∈ remainderBirthTarget L w k := by
        simp only [remainderBirthTarget, mem_interval]
        have hxL := x.isLt
        omega
      obtain ⟨hB, hleft⟩ := passed_targets_of_le k x (by omega)
      simp [afterLeftTransfer, afterBlockBirth, afterRemainderBirth,
        Frame.changeOwner, hR, hB, hleft]

/-- The four specified owner changes give exactly the next stage, including
stage zero. No ownership recurrence is assumed.
Source: Part II, `prop:sweep`, lines 375–376. -/
theorem afterRightTransfer_eq_stageFrame (hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    afterRightTransfer L w q pos k = stageFrame L w q pos k.succ := by
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  have howner : (afterRightTransfer L w q pos k).owner = stageOwner L w k.succ := by
    funext x
    by_cases hx : x.val < k.val * (20 * w)
    · have hnext : x.val < (k.val + 1) * (20 * w) := by omega
      obtain ⟨hR, hB⟩ := unused_births_of_lt k x (by omega)
      have hleft : x ∉ leftBandTarget L w k := by
        simp only [leftBandTarget, mem_interval]
        omega
      have hright : x ∉ rightBandTarget L w k := by
        simp only [rightBandTarget, mem_interval]
        omega
      simp [afterRightTransfer, afterLeftTransfer, afterBlockBirth,
        afterRemainderBirth, Frame.changeOwner, stageFrame, Frame.raw, stageOwner,
        hR, hB, hleft, hright, hx, hnext]
    · by_cases hmid : x.val < (k.val + 1) * (20 * w)
      · have hnext : stageOwner L w k.succ x = Sum.inr k :=
          stageOwner_at_block hw k.succ k x (by simp) (by omega) hmid
        rw [hnext]
        have hR : x ∉ remainderBirthTarget L w k := by
          simp only [remainderBirthTarget, mem_interval]
          omega
        have hright : x ∉ rightBandTarget L w k := by
          simp only [rightBandTarget, mem_interval]
          omega
        by_cases hband : x.val < k.val * (20 * w) + w
        · have hleft : x ∈ leftBandTarget L w k := by
            simp only [leftBandTarget, mem_interval]
            omega
          simp [afterRightTransfer, afterLeftTransfer, Frame.changeOwner, hright, hleft]
        · have hleft : x ∉ leftBandTarget L w k := by
            simp only [leftBandTarget, mem_interval]
            omega
          have hB : x ∈ blockBirthTarget L w k := by
            simp only [blockBirthTarget, mem_interval]
            omega
          simp [afterRightTransfer, afterLeftTransfer, afterBlockBirth,
            Frame.changeOwner, hright, hleft, hB]
      · have hnext : stageOwner L w k.succ x = Sum.inl k.succ := by
          simp [stageOwner, hmid]
        rw [hnext]
        by_cases hband : x.val < (k.val + 1) * (20 * w) + w
        · have hright : x ∈ rightBandTarget L w k := by
            simp only [rightBandTarget, mem_interval]
            omega
          simp [afterRightTransfer, Frame.changeOwner, hright]
        · have hR : x ∈ remainderBirthTarget L w k := by
            simp only [remainderBirthTarget, mem_interval]
            have hxL := x.isLt
            omega
          obtain ⟨hB, hleft⟩ := passed_targets_of_le k x (by omega)
          have hright : x ∉ rightBandTarget L w k := by
            simp only [rightBandTarget, mem_interval]
            omega
          simp [afterRightTransfer, afterLeftTransfer, afterBlockBirth,
            afterRemainderBirth, Frame.changeOwner, hR, hB, hleft, hright]
  exact (raw_owner_eq (afterRightTransfer L w q pos k) rfl).symm.trans
    (congrArg (Frame.raw (pos := pos) (q := q)) howner)

/-- The actual main frame after the corrected left-band construction, except
that stage zero uses the prescribed direct death. The previous completed party
is introduced only in the positive-stage branch.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
def leftBandMain (L w q : ℕ) (pos : Fin L → ℝ × ℝ)
    (k : Fin (stageCount L w)) : Frame pos q (Party L w) :=
  if k.val = 0 then afterLeftTransfer L w q pos k
  else OneBand.main₈ (afterBlockBirth L w q pos k).owner
    (.inl k.castSucc) (.inr k)
    (.inr ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩)
    (k.val * (20 * w)) w

/-- The actual main frame after the corrected right-band construction, using
the main frame produced by the left construction.
Source: Part II, `con:sweep`, move (4), lines 339–340. -/
def rightBandMain (L w q : ℕ) (pos : Fin L → ℝ × ℝ)
    (k : Fin (stageCount L w)) : Frame pos q (Party L w) :=
  OneBand.main₈ (leftBandMain L w q pos k).owner
    (.inl k.castSucc) (.inl k.succ) (.inr k) ((k.val + 1) * (20 * w)) w

/-- The actual left-band frame has the specified transfer endpoint. The band
margins and owner hypotheses are derived from the constructed stage.
Source: Part II, `prop:sweep`, lines 370–374. -/
theorem leftBandMain_eq_afterLeftTransfer (hw : 1 ≤ w)
    (hL : 3 * (20 * w) ≤ L) (k : Fin (stageCount L w)) :
    leftBandMain L w q pos k = afterLeftTransfer L w q pos k := by
  unfold leftBandMain
  split_ifs with hk
  · rfl
  · have hkpos : 0 < k.val := by omega
    obtain ⟨hC, hA, hB⟩ := left_band_owners (pos := pos) (q := q) hw k hkpos
    have hleft : 8 * w ≤ k.val * (20 * w) := stage_left_margin w k.val (by omega)
    have hmargin := stage_right_margin L w hL k
    have hright : k.val * (20 * w) + 2 * w ≤ L := by nlinarith
    have he := OneBand.main₈_eq_changeOwner (pos := pos) (q := q)
      (afterBlockBirth L w q pos k).owner
      (.inl k.castSucc) (.inr k)
      (.inr ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩)
      (k.val * (20 * w)) w hw hleft hright hC hA hB
    simpa only [OneBand.main₀, raw_owner_eq (afterBlockBirth L w q pos k) rfl,
      afterLeftTransfer, leftBandTarget] using he

/-- The actual right-band frame has the specified transfer endpoint. No final
ownership identity or band hypothesis is supplied as an additional premise.
Source: Part II, `prop:sweep`, lines 374–376. -/
theorem rightBandMain_eq_afterRightTransfer (hw : 1 ≤ w)
    (hL : 3 * (20 * w) ≤ L) (k : Fin (stageCount L w)) :
    rightBandMain L w q pos k = afterRightTransfer L w q pos k := by
  unfold rightBandMain
  rw [leftBandMain_eq_afterLeftTransfer hw hL k]
  obtain ⟨hC, hA, hB⟩ := right_band_owners (pos := pos) (q := q) hw k
  have hleft : 8 * w ≤ (k.val + 1) * (20 * w) :=
    stage_left_margin w (k.val + 1) (by omega)
  have hmargin := stage_right_margin L w hL k
  have hright : (k.val + 1) * (20 * w) + 2 * w ≤ L := by nlinarith
  have he := OneBand.main₈_eq_changeOwner (pos := pos) (q := q)
    (afterLeftTransfer L w q pos k).owner
    (.inl k.castSucc) (.inl k.succ) (.inr k) ((k.val + 1) * (20 * w)) w
    hw hleft hright hC hA hB
  simpa only [OneBand.main₀, raw_owner_eq (afterLeftTransfer L w q pos k) rfl,
    afterRightTransfer, rightBandTarget] using he

/-- The actual corrected band frames complete the next main-sheet stage,
including the exceptional first stage. This is a frame identity, not yet the
construction of its quantum circuit or information bounds.
Source: Part II, `prop:sweep`, lines 375–376. -/
theorem rightBandMain_eq_stageFrame (hw : 1 ≤ w)
    (hL : 3 * (20 * w) ≤ L) (k : Fin (stageCount L w)) :
    rightBandMain L w q pos k = stageFrame L w q pos k.succ := by
  rw [rightBandMain_eq_afterRightTransfer hw hL k, afterRightTransfer_eq_stageFrame hw k]

end TNLean.MPS.AreaLaw.ChainSweep
