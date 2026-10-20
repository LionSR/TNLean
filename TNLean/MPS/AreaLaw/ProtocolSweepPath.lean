/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepHistory

/-!
# The frame lists between the operations of the chain sweep

Each stage has eighteen operations and nineteen boundaries: two births,
eight left-band operations and eight right-band operations. At stage zero
the left transfer is a direct death followed by seven identity operations.
Every auxiliary occurrence retains its original label. During a band the
selected occurrence is next to the main sheet; at the band endpoint the
original order is restored by a private permutation.

The definitions use the actual intermediate one-band frames, rather than
only their desired owners. The natural-number sequence is obtained from
the stage and local boundary by division with remainder. Its initial and
terminal identities follow from the previously derived frame history.
This file does not construct the circuits or assume a trajectory or its
error estimate.

Source: the one-dimensional note, Part II, `con:sweep`, lines 330–343,
and `prop:sweep`, proof, lines 365–378.

**Local fix (terminal auxiliary registers):** Retired copies keep their
actual A and B strips and C-owned exterior. Integer-ended bands are
half-open. See
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.PEPS.EncodedFrame

variable {L w q : ℕ}

/-- Erasing a label uses its equality predicate under any lawful equality test. -/
private theorem erase_eq_eraseP_decide {X : Type*} [BEq X] [LawfulBEq X]
    [DecidableEq X] (l : List X) (c : X) :
    l.erase c = l.eraseP (fun y ↦ decide (c = y)) := by
  simp only [List.erase_eq_eraseP, Bool.beq_eq_decide_eq]

/-- A frame without holes is the raw frame of its actual owner. -/
private theorem raw_owner_eq (F : Sheet (Fin L) (Party L w)) (hF : F.holes = []) :
    Sheet.mk F.owner = F := by
  cases F with
  | mk owner holes disjoint => cases hF; rfl

/-- The actual left endpoint has no holes, in either the direct-death or
the band branch. Source: Part II, `con:sweep`, move (3), lines 336–338. -/
private theorem raw_leftBandMain (k : Fin (stageCount L w)) :
    Sheet.mk (leftBandMain L w k).owner = leftBandMain L w k := by
  apply raw_owner_eq
  unfold leftBandMain
  split_ifs <;> rfl

/-- The selected left label denotes precisely the actual auxiliary endpoint
of the current left band. The predecessor is introduced only under hk.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
private theorem retiredAuxiliaryFrame_leftCopyLabel (k : Fin (stageCount L w))
    (hk : 0 < k.val) :
    retiredAuxiliaryFrame L w (leftCopyLabel L w k hk) =
      OneBand.aux₄ (afterBlockBirth L w k).owner
        (.inl k.castSucc) (.inr k)
        (.inr ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩)
        (k.val * (20 * w)) w := by
  have he : k.val - 1 + 1 = k.val := by omega
  let k' : Fin (stageCount L w) := ⟨k.val - 1 + 1, by omega⟩
  have hk' : k' = k := Fin.ext he
  change OneBand.aux₄ (afterBlockBirth L w k').owner
      (.inl k'.castSucc) (.inr k')
      (.inr ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩)
      ((k.val - 1 + 1) * (20 * w)) w = _
  rw [hk', he]

/-- The actual left-band pair with all other labelled copies untouched.
Only the positive-stage branch has a left copy.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
def leftBandFrames (L w : ℕ)
    (k : Fin (stageCount L w)) (hk : 0 < k.val) (j : ℕ) :
    List (Sheet (Fin L) (Party L w)) :=
  OneBand.frames (afterBlockBirth L w k).owner
      (.inl k.castSucc) (.inr k)
      (.inr ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩)
      (k.val * (20 * w)) w j ++
    ((initialAuxiliaryOrder L w).erase (leftCopyLabel L w k hk)).map
      (auxiliaryFrameBefore L w k.val)

/-- The right-band pair uses the actual left-band output, and its spectators
already contain the retired left copy when present.
Source: Part II, `con:sweep`, move (4), lines 339–340. -/
def rightBandFrames (L w : ℕ)
    (k : Fin (stageCount L w)) (j : ℕ) : List (Sheet (Fin L) (Party L w)) :=
  OneBand.frames (leftBandMain L w k).owner
      (.inl k.castSucc) (.inl k.succ) (.inr k) ((k.val + 1) * (20 * w)) w j ++
    ((initialAuxiliaryOrder L w).erase (.inl k)).map (leftAuxiliaryFrame L w k)

/-- The nineteen actual frame boundaries of one stage. Values beyond the
eighteenth boundary stay at that stage's endpoint. The seven identity
operations at the first left transfer introduce no fictitious copy.
Source: Part II, `con:sweep`, lines 330–343, and `prop:sweep`, lines 373–378. -/
def stageBoundaryFrames (L w : ℕ)
    (k : Fin (stageCount L w)) (j : ℕ) : List (Sheet (Fin L) (Party L w)) :=
  if j = 0 then sweepFrames L w k.castSucc
  else if j = 1 then
    afterRemainderBirth L w k ::
      (initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val)
  else if j = 2 then
    afterBlockBirth L w k ::
      (initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val)
  else if j < 10 then
    if hk : 0 < k.val then leftBandFrames L w k hk (j - 2)
    else afterLeftFrames L w k
  else if j = 10 then afterLeftFrames L w k
  else if j < 18 then rightBandFrames L w k (j - 10)
  else afterRightFrames L w k

/-- The actual number of elementary operations in the eighteen-slot sweep.
Identity operations in the exceptional first stage are included.
Source: Part II, `prop:sweep`, proof, lines 376–378. -/
def sweepOperationCount (L w : ℕ) : ℕ := 18 * stageCount L w

/-- The complete sequence of frame lists. After its last actual operation
the sequence remains at the specified terminal list. The connection to the
last actual stage is derived below, rather than assumed.
Source: Part II, `prop:sweep`, proof, lines 365–378. -/
def operationFrames (L w : ℕ) (n : ℕ) :
    List (Sheet (Fin L) (Party L w)) :=
  if hn : n < sweepOperationCount L w then
    stageBoundaryFrames L w
      ⟨n / 18, (Nat.div_lt_iff_lt_mul (by decide)).2 (by
        simpa only [sweepOperationCount, Nat.mul_comm] using hn)⟩ (n % 18)
  else terminalFrames L w

/-- The zeroth boundary is the actual input of the stage.
Source: Part II, `con:sweep`, lines 331–332. -/
theorem stageBoundaryFrames_zero (k : Fin (stageCount L w)) :
    stageBoundaryFrames L w k 0 = sweepFrames L w k.castSucc := by
  simp [stageBoundaryFrames]

/-- The first boundary records only the first birth.
Source: Part II, `con:sweep`, move (1), line 334. -/
theorem stageBoundaryFrames_one (k : Fin (stageCount L w)) :
    stageBoundaryFrames L w k 1 =
      afterRemainderBirth L w k ::
        (initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val) := by
  simp [stageBoundaryFrames]

/-- The second boundary records both births and no auxiliary change.
Source: Part II, `con:sweep`, moves (1)–(2), lines 334–335. -/
theorem stageBoundaryFrames_two (k : Fin (stageCount L w)) :
    stageBoundaryFrames L w k 2 =
      afterBlockBirth L w k ::
        (initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val) := by
  simp [stageBoundaryFrames]

/-- The positive-stage left interior uses the corresponding actual band pair.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
theorem stageBoundaryFrames_left (k : Fin (stageCount L w)) (hk : 0 < k.val)
    {j : ℕ} (hlo : 3 ≤ j) (hhi : j < 10) :
    stageBoundaryFrames L w k j = leftBandFrames L w k hk (j - 2) := by
  simp [stageBoundaryFrames, show j ≠ 0 by omega, show j ≠ 1 by omega,
    show j ≠ 2 by omega, hhi, hk]

/-- The exceptional left transfer is a direct death followed by identities.
No auxiliary occurrence is selected in this branch.
Source: Part II, `con:sweep`, move (3), lines 337–338. -/
theorem stageBoundaryFrames_first_left (k : Fin (stageCount L w)) (hk : k.val = 0)
    {j : ℕ} (hlo : 3 ≤ j) (hhi : j ≤ 10) :
    stageBoundaryFrames L w k j = afterLeftFrames L w k := by
  by_cases hj : j < 10
  · simp [stageBoundaryFrames, show j ≠ 0 by omega, show j ≠ 1 by omega,
      show j ≠ 2 by omega, hj, hk]
  · have he : j = 10 := by omega
    simp [stageBoundaryFrames, he]

/-- At boundary ten the complete original copy order has been restored.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
theorem stageBoundaryFrames_ten (k : Fin (stageCount L w)) :
    stageBoundaryFrames L w k 10 = afterLeftFrames L w k := by
  simp [stageBoundaryFrames]

/-- At the first stage the third boundary is the actual direct death on
the main sheet, with every auxiliary occurrence unchanged.
Source: Part II, `con:sweep`, move (3), lines 337–338. -/
theorem stageBoundaryFrames_first_death (k : Fin (stageCount L w)) (hk : k.val = 0) :
    stageBoundaryFrames L w k 3 =
      (afterBlockBirth L w k).changeOwner (leftBandTarget L w k) (.inr k) ::
        (initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val) := by
  rw [stageBoundaryFrames_first_left k hk (by decide) (by decide)]
  simp only [afterLeftFrames, leftBandMain, ite_eq_left hk,
    leftAuxiliaryFrame_zero k hk, afterLeftTransfer]

/-- The right interior uses the actual right-band pair.
Source: Part II, `con:sweep`, move (4), lines 339–340. -/
theorem stageBoundaryFrames_right (k : Fin (stageCount L w)) {j : ℕ}
    (hlo : 11 ≤ j) (hhi : j < 18) :
    stageBoundaryFrames L w k j = rightBandFrames L w k (j - 10) := by
  simp [stageBoundaryFrames, show j ≠ 0 by omega, show j ≠ 1 by omega,
    show j ≠ 2 by omega, show ¬j < 10 by omega, show j ≠ 10 by omega, hhi]

/-- At and beyond the eighteenth boundary the actual right endpoint is used.
Source: Part II, `con:sweep`, move (4), lines 339–342. -/
theorem stageBoundaryFrames_last (k : Fin (stageCount L w)) {j : ℕ} (hj : 18 ≤ j) :
    stageBoundaryFrames L w k j = afterRightFrames L w k := by
  simp [stageBoundaryFrames, show j ≠ 0 by omega, show j ≠ 1 by omega,
    show j ≠ 2 by omega, show ¬j < 10 by omega, show j ≠ 10 by omega,
    show ¬j < 18 by omega]

/-- The end of an actual stage is its next actual stage input, with all
original auxiliary occurrences. Source: Part II, `prop:sweep`, lines 375–378. -/
theorem stageBoundaryFrames_eighteen (k : Fin (stageCount L w)) :
    stageBoundaryFrames L w k 18 = sweepFrames L w k.succ := by
  rw [stageBoundaryFrames_last k le_rfl, afterRightFrames_eq_sweepFrames]

/-- The first left-band operation may bring forward its unused original
copy by a private permutation. Selection is by label, not by frame value.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
theorem stageBoundaryFrames_left_entrance_perm (k : Fin (stageCount L w))
    (hk : 0 < k.val) :
    (stageBoundaryFrames L w k 2).Perm (leftBandFrames L w k hk 0) := by
  rw [stageBoundaryFrames_two]
  change (_ :: _).Perm
    (Sheet.mk (afterBlockBirth L w k).owner ::
      Sheet.mk (fun _ ↦ Sum.inr
        (⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ : Fin (stageCount L w))) :: _)
  rw [raw_owner_eq (afterBlockBirth L w k) rfl]
  have haux : Sheet.mk
      (fun _ ↦ Sum.inr
        (⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ : Fin (stageCount L w))) =
      auxiliaryFrameBefore L w k.val (leftCopyLabel L w k hk) := by
    rw [auxiliaryFrameBefore_left_unused k hk]
    rfl
  rw [haux]
  change (afterBlockBirth L w k ::
      (initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val)).Perm
    (afterBlockBirth L w k ::
      auxiliaryFrameBefore L w k.val (leftCopyLabel L w k hk) ::
        ((initialAuxiliaryOrder L w).erase (leftCopyLabel L w k hk)).map
          (auxiliaryFrameBefore L w k.val))
  have hc : leftCopyLabel L w k hk ∈ initialAuxiliaryOrder L w := by
    simp [initialAuxiliaryOrder]
  simpa only [erase_eq_eraseP_decide] using
    (perm_map_cons (X := AuxiliaryCopy L w) (afterBlockBirth L w k)
      (l := initialAuxiliaryOrder L w) (x := leftCopyLabel L w k hk) hc
      (auxiliaryFrameBefore L w k.val)).trans (List.Perm.swap _ _ _)

/-- The last left-band operation restores the original list order with
precisely its own copy retired. No distinctness of frame values is needed.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
theorem leftBandFrames_eight_perm (k : Fin (stageCount L w)) (hk : 0 < k.val) :
    (leftBandFrames L w k hk 8).Perm (afterLeftFrames L w k) := by
  have hp := perm_map_update_cons (leftBandMain L w k)
    (l := initialAuxiliaryOrder L w) (x := leftCopyLabel L w k hk)
    (Finset.nodup_toList _) (by simp [initialAuxiliaryOrder])
    (auxiliaryFrameBefore L w k.val)
    (retiredAuxiliaryFrame L w (leftCopyLabel L w k hk))
  have hk0 : k.val ≠ 0 := by omega
  rw [retiredAuxiliaryFrame_leftCopyLabel k hk] at hp
  simpa only [leftBandFrames, OneBand.frames, List.cons_append, List.nil_append,
    afterLeftFrames, leftAuxiliaryFrame_eq_update k hk,
    retiredAuxiliaryFrame_leftCopyLabel k hk, leftBandMain, ite_eq_right hk0,
    erase_eq_eraseP_decide] using
    (hp.trans (List.Perm.swap _ _ _)).symm

/-- The first right-band operation selects its original unused right copy.
Source: Part II, `con:sweep`, move (4), lines 339–340. -/
theorem stageBoundaryFrames_right_entrance_perm (k : Fin (stageCount L w)) :
    (stageBoundaryFrames L w k 10).Perm (rightBandFrames L w k 0) := by
  rw [stageBoundaryFrames_ten]
  change (_ :: _).Perm
    (Sheet.mk (leftBandMain L w k).owner :: Sheet.mk (fun _ ↦ Sum.inr k) :: _)
  rw [raw_leftBandMain k]
  have haux : Sheet.mk (fun _ ↦ Sum.inr k) =
      leftAuxiliaryFrame L w k (.inl k) := by
    rw [leftAuxiliaryFrame_right_unused]
    rfl
  rw [haux]
  change (leftBandMain L w k ::
      (initialAuxiliaryOrder L w).map (leftAuxiliaryFrame L w k)).Perm
    (leftBandMain L w k :: leftAuxiliaryFrame L w k (Sum.inl k) ::
      ((initialAuxiliaryOrder L w).erase (Sum.inl k)).map (leftAuxiliaryFrame L w k))
  have hc : (Sum.inl k : AuxiliaryCopy L w) ∈ initialAuxiliaryOrder L w := by
    simp [initialAuxiliaryOrder]
  simpa only [erase_eq_eraseP_decide] using
    (perm_map_cons (X := AuxiliaryCopy L w) (leftBandMain L w k)
      (l := initialAuxiliaryOrder L w) (x := Sum.inl k) hc
      (leftAuxiliaryFrame L w k)).trans (List.Perm.swap _ _ _)

/-- The last right-band operation restores the original auxiliary order
with precisely that right copy retired.
Source: Part II, `con:sweep`, move (4), lines 339–342. -/
theorem rightBandFrames_eight_perm (k : Fin (stageCount L w)) :
    (rightBandFrames L w k 8).Perm (afterRightFrames L w k) := by
  have hp := perm_map_update_cons (rightBandMain L w k)
    (l := initialAuxiliaryOrder L w) (x := Sum.inl k)
    (Finset.nodup_toList _) (by simp [initialAuxiliaryOrder])
    (leftAuxiliaryFrame L w k) (rightRetiredAuxiliary L w k)
  simpa only [rightBandFrames, OneBand.frames, List.cons_append, List.nil_append,
    afterRightFrames, rightBandMain, rightRetiredAuxiliary, erase_eq_eraseP_decide] using
    (hp.trans (List.Perm.swap _ _ _)).symm

/-- The sequence is stationary after the last actual operation.
Source: Part II, `con:sweep`, line 342. -/
theorem operationFrames_of_le {n : ℕ} (hn : sweepOperationCount L w ≤ n) :
    operationFrames L w n = terminalFrames L w := by
  simp [operationFrames, not_lt.mpr hn]

/-- Every complete stage boundary in the natural-number sequence is the
derived labelled history boundary, including the final boundary.
Source: Part II, `prop:sweep`, proof, lines 365–378. -/
theorem operationFrames_stage (k : Fin (stageCount L w + 1)) :
    operationFrames L w (18 * k.val) = sweepFrames L w k := by
  by_cases hk : k.val < stageCount L w
  · have hn : 18 * k.val < sweepOperationCount L w := by
      unfold sweepOperationCount
      omega
    unfold operationFrames
    rw [dite_eq_left hn]
    have hdiv : 18 * k.val / 18 = k.val := by omega
    have hmod : 18 * k.val % 18 = 0 := by omega
    let k' : Fin (stageCount L w) := ⟨k.val, hk⟩
    have he : (⟨18 * k.val / 18, by omega⟩ : Fin (stageCount L w)) = k' :=
      Fin.ext hdiv
    rw [he, hmod, stageBoundaryFrames_zero]
    have he' : k'.castSucc = k := Fin.ext rfl
    rw [he']
  · have he : k = Fin.last (stageCount L w) := by
      apply Fin.ext
      change k.val = stageCount L w
      omega
    have hn : sweepOperationCount L w ≤ 18 * k.val := by
      unfold sweepOperationCount
      omega
    rw [operationFrames_of_le hn, he, sweepFrames_last]

/-- The initial frame list is derived even when there are no stages.
Source: Part II, `prop:sweep`, item (1), lines 350–353. -/
theorem operationFrames_zero (L w : ℕ) :
    operationFrames L w 0 = initialFrames L w := by
  simpa only [Fin.val_zero, mul_zero, sweepFrames_zero] using
    (operationFrames_stage (L := L) (w := w) (q := q) 0)

/-- The actual last operation has the already specified terminal list.
Source: Part II, `prop:sweep`, item (3), lines 355–360. -/
theorem operationFrames_last :
    operationFrames L w (sweepOperationCount L w) = terminalFrames L w :=
  operationFrames_of_le le_rfl

/-- Each local boundary, including the last one, is the corresponding
natural-number boundary. At the last boundary this uses the proved stage
recurrence, rather than a supplied equality.
Source: Part II, `prop:sweep`, proof, lines 375–378. -/
theorem operationFrames_stageBoundary (k : Fin (stageCount L w)) (j : Fin 19) :
    operationFrames L w (18 * k.val + j.val) =
      stageBoundaryFrames L w k j.val := by
  by_cases hj : j.val < 18
  · have hn : 18 * k.val + j.val < sweepOperationCount L w := by
      have hk := k.isLt
      unfold sweepOperationCount
      omega
    unfold operationFrames
    rw [dite_eq_left hn]
    have hdiv : (18 * k.val + j.val) / 18 = k.val := by omega
    have hmod : (18 * k.val + j.val) % 18 = j.val := by omega
    have he : (⟨(18 * k.val + j.val) / 18,
        by have hk := k.isLt; omega⟩ : Fin (stageCount L w)) = k := Fin.ext hdiv
    rw [he, hmod]
  · have he : j.val = 18 := by have hj' := j.isLt; omega
    rw [he, show 18 * k.val + 18 = 18 * k.succ.val by
      simp only [Fin.val_succ]
      omega,
      operationFrames_stage, stageBoundaryFrames_eighteen]

/-- The source and target of every actual operation are the corresponding
two local boundaries, including the last operation of every stage. This is
the equality needed when inserting the local circuits in the total sequence.
Source: Part II, `prop:sweep`, proof, lines 375–378. -/
theorem operationFrames_step (k : Fin (stageCount L w)) (j : Fin 18) :
    operationFrames L w (18 * k.val + j.val) =
        stageBoundaryFrames L w k j.val ∧
      operationFrames L w (18 * k.val + j.val + 1) =
        stageBoundaryFrames L w k (j.val + 1) := by
  constructor
  · exact operationFrames_stageBoundary k j.castSucc
  · simpa only [Fin.val_succ, Nat.add_assoc] using
      (operationFrames_stageBoundary (q := q) k j.succ)

end TNLean.MPS.AreaLaw.ChainSweep
