/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolRetiredAuxiliary
import TNLean.MPS.AreaLaw.ProtocolTerminalReference
import TNLean.PEPS.Approximation.DyadicProtocolStack

/-!
# The labelled auxiliary frames at successive chain stages

The main frame is followed by every original auxiliary copy in its initial
label order. A copy remains at its initial holder until its prescribed band
operation, and then retains the actual auxiliary frame of that operation.
Right copy j is used at stage j; left copy j is used at stage j+1. Stage zero
has no left copy. Equal band centres never identify the two copy labels.

These are identities of actual frame lists and single-label replacements.
They do not construct the gates or establish a vector-error estimate. The
terminal list identity uses the previously specified one-band auxiliary
endpoints; it does not assume that a circuit has reached that list.

Source: the one-dimensional note, Part II, `part2b_mps_protocol.tex`,
Construction `con:sweep`, lines 330–343, and Proposition `prop:sweep`,
lines 350–378.

**Local fix (terminal auxiliary registers):** Retired auxiliary frames retain
their actual A and B strips and their C-owned exterior. The existing
half-open convention and physical/private distinction are recorded in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.PEPS.EncodedFrame

variable {L w q : ℕ}

/-- The stage of the original labelled copy's band operation.
Source: Part II, `con:sweep`, moves (3)–(4), lines 336–340. -/
def auxiliaryStage (L w : ℕ) : AuxiliaryCopy L w → ℕ
  | .inl j => j.val
  | .inr j => j.val + 1

/-- The actual band auxiliary endpoint at its original copy label.
Source: Part II, `con:band`, lines 271–272, and `con:sweep`, lines 336–340. -/
def retiredAuxiliaryFrame (L w : ℕ) :
    AuxiliaryCopy L w → Sheet (Fin L) (Party L w)
  | .inl j => rightRetiredAuxiliary L w j
  | .inr j => leftRetiredAuxiliary L w j

/-- Before stage s, only copies whose own band stage is earlier have retired.
The other copies remain the original raw sheets at their initial holders.
Source: Part II, `con:sweep`, lines 330–340, and `prop:sweep`, lines 350–359. -/
def auxiliaryFrameBefore (L w : ℕ) (s : ℕ)
    (c : AuxiliaryCopy L w) : Sheet (Fin L) (Party L w) :=
  if auxiliaryStage L w c < s then retiredAuxiliaryFrame L w c
  else Sheet.mk (fun _ ↦ initialAuxiliaryHolder L w c)

/-- The main frame and all original auxiliary occurrences before a stage.
Source: Part II, `prop:sweep`, proof, lines 365–378. -/
def sweepFrames (L w : ℕ)
    (k : Fin (stageCount L w + 1)) : List (Sheet (Fin L) (Party L w)) :=
  stageFrame L w k ::
    (initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val)

/-- After the left transfer, its positive-stage left copy has retired and
the current right copy has not yet been used.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
def leftAuxiliaryFrame (L w : ℕ)
    (k : Fin (stageCount L w)) : AuxiliaryCopy L w → Sheet (Fin L) (Party L w)
  | .inl j => auxiliaryFrameBefore L w k.val (.inl j)
  | .inr j =>
      if j.val + 1 ≤ k.val then leftRetiredAuxiliary L w j
      else Sheet.mk (fun _ ↦ initialAuxiliaryHolder L w (.inr j))

/-- The actual main endpoint and the same labelled list after the left transfer.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
def afterLeftFrames (L w : ℕ)
    (k : Fin (stageCount L w)) : List (Sheet (Fin L) (Party L w)) :=
  leftBandMain L w k ::
    (initialAuxiliaryOrder L w).map (leftAuxiliaryFrame L w k)

/-- The right transfer changes its actual copy occurrence in that same list.
Source: Part II, `con:sweep`, move (4), lines 339–340. -/
def afterRightFrames (L w : ℕ)
    (k : Fin (stageCount L w)) : List (Sheet (Fin L) (Party L w)) :=
  rightBandMain L w k ::
    (initialAuxiliaryOrder L w).map
      (Function.update (leftAuxiliaryFrame L w k) (.inl k)
        (rightRetiredAuxiliary L w k))

/-- The left copy exists only at a positive stage. Its index is k−1, while
its actual band stage is k. Source: Part II, `con:sweep`, lines 336–338. -/
def leftCopyLabel (L w : ℕ) (k : Fin (stageCount L w)) (hk : 0 < k.val) :
    AuxiliaryCopy L w :=
  .inr ⟨k.val - 1, by omega⟩

/-- Every original copy is used before the final stage boundary.
Source: Part II, `con:sweep`, lines 330–340. -/
theorem auxiliaryStage_lt_stageCount (c : AuxiliaryCopy L w) :
    auxiliaryStage L w c < stageCount L w := by
  cases c with
  | inl j => exact j.isLt
  | inr j =>
      change j.val + 1 < stageCount L w
      have hj := j.isLt
      omega

/-- An existing copy or actual stage forces the required geometric margins.
Source: Part II, `eq:blocks`, the parameter choice at lines 247–255. -/
private theorem geometry_of_stageCount_pos (hm : 0 < stageCount L w) :
    1 ≤ w ∧ 3 * (20 * w) ≤ L := by
  have hw : 0 < w := by
    by_contra h
    have hw0 : w = 0 := by omega
    simp [stageCount, hw0] at hm
  have ht : 0 < 20 * w := by omega
  have hdiv : 3 ≤ L / (20 * w) := by
    unfold stageCount at hm
    omega
  exact ⟨hw, (Nat.le_div_iff_mul_le ht).1 hdiv⟩

/-- Initially no auxiliary copy has been used.
Source: Part II, `prop:sweep`, item (1), lines 350–353. -/
theorem auxiliaryFrameBefore_zero (c : AuxiliaryCopy L w) :
    auxiliaryFrameBefore L w 0 c =
      Sheet.mk (fun _ ↦ initialAuxiliaryHolder L w c) := by
  simp [auxiliaryFrameBefore]

/-- The last boundary retains every actual retired auxiliary endpoint in
the previously specified raw copy coordinates. No endpoint identity is assumed.
Source: Part II, `con:band`, lines 271–272, and `prop:sweep`, lines 356–359. -/
theorem auxiliaryFrameBefore_last (c : AuxiliaryCopy L w) :
    auxiliaryFrameBefore L w (stageCount L w) c =
      Sheet.mk (fun x ↦ auxiliaryOwner L w (c, x)) := by
  obtain ⟨hw, hL⟩ := geometry_of_stageCount_pos
    ((Nat.zero_le (auxiliaryStage L w c)).trans_lt (auxiliaryStage_lt_stageCount c))
  rw [auxiliaryFrameBefore, ite_eq_left (auxiliaryStage_lt_stageCount c)]
  cases c with
  | inl j => exact rightRetiredAuxiliary_eq_raw hw hL j
  | inr j => exact leftRetiredAuxiliary_eq_raw hw hL j

/-- The complete initial list is derived from the actual stage-zero owner
and the unused labelled copies. Source: Part II, `prop:sweep`, lines 350–353. -/
theorem sweepFrames_zero (L w : ℕ) :
    sweepFrames L w 0 = initialFrames L w := by
  simp [sweepFrames, stageFrame, stageOwner_zero, auxiliaryFrameBefore_zero,
    initialFrames]

/-- The complete terminal list follows from the derived main and auxiliary
endpoints. Source: Part II, `prop:sweep`, lines 355–360. -/
theorem sweepFrames_last :
    sweepFrames L w (Fin.last (stageCount L w)) = terminalFrames L w := by
  simp [sweepFrames, stageFrame, stageOwner_last, terminalFrames,
    terminalAuxiliaryFrames, auxiliaryFrameBefore_last]

/-- The current right copy is unused before its right-band operation.
Source: Part II, `con:sweep`, move (4), lines 339–340. -/
theorem leftAuxiliaryFrame_right_unused (k : Fin (stageCount L w)) :
    leftAuxiliaryFrame L w k (.inl k) =
      Sheet.mk (fun _ ↦ initialAuxiliaryHolder L w (.inl k)) := by
  simp [leftAuxiliaryFrame, auxiliaryFrameBefore, auxiliaryStage]

/-- The selected positive-stage left copy is still unused before its operation.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
theorem auxiliaryFrameBefore_left_unused (k : Fin (stageCount L w)) (hk : 0 < k.val) :
    auxiliaryFrameBefore L w k.val (leftCopyLabel L w k hk) =
      Sheet.mk (fun _ ↦ initialAuxiliaryHolder L w (leftCopyLabel L w k hk)) := by
  have he : k.val - 1 + 1 = k.val := by omega
  simp [auxiliaryFrameBefore, leftCopyLabel, auxiliaryStage, he]

/-- The exceptional first left transfer retires no auxiliary copy.
Source: Part II, `con:sweep`, move (3), lines 337–338. -/
theorem leftAuxiliaryFrame_zero (k : Fin (stageCount L w)) (hk : k.val = 0) :
    leftAuxiliaryFrame L w k = auxiliaryFrameBefore L w k.val := by
  funext c
  cases c with
  | inl j => rfl
  | inr j => simp [leftAuxiliaryFrame, auxiliaryFrameBefore, auxiliaryStage, hk]

/-- At a positive stage, precisely its original left-copy occurrence changes.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
theorem leftAuxiliaryFrame_eq_update (k : Fin (stageCount L w)) (hk : 0 < k.val) :
    leftAuxiliaryFrame L w k =
      Function.update (auxiliaryFrameBefore L w k.val) (leftCopyLabel L w k hk)
        (retiredAuxiliaryFrame L w (leftCopyLabel L w k hk)) := by
  funext c
  cases c with
  | inl j => simp [leftAuxiliaryFrame, leftCopyLabel]
  | inr j =>
      by_cases hj : j.val + 1 = k.val
      · have he : (Sum.inr j : AuxiliaryCopy L w) = leftCopyLabel L w k hk := by
          apply congrArg Sum.inr
          apply Fin.ext
          change j.val = k.val - 1
          omega
        rw [← he]
        simp [leftAuxiliaryFrame, retiredAuxiliaryFrame, hj]
      · have hne : Sum.inr j ≠ leftCopyLabel L w k hk := by
          intro h
          have hv := congrArg (fun c : AuxiliaryCopy L w ↦ auxiliaryStage L w c) h
          simp only [leftCopyLabel, auxiliaryStage] at hv
          omega
        rw [Function.update_of_ne hne]
        by_cases hlt : j.val + 1 < k.val
        · simp [leftAuxiliaryFrame, auxiliaryFrameBefore, auxiliaryStage,
            retiredAuxiliaryFrame, hlt, hlt.le]
        · have hle : ¬ j.val + 1 ≤ k.val := by omega
          simp [leftAuxiliaryFrame, auxiliaryFrameBefore, auxiliaryStage,
            hlt, hle]

/-- All other original copy occurrences are spectators of the left transfer.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
theorem leftAuxiliaryFrame_spectator (k : Fin (stageCount L w)) (hk : 0 < k.val)
    (c : AuxiliaryCopy L w) (hc : c ≠ leftCopyLabel L w k hk) :
    leftAuxiliaryFrame L w k c = auxiliaryFrameBefore L w k.val c := by
  rw [leftAuxiliaryFrame_eq_update k hk, Function.update_of_ne hc]

/-- Retiring the current right copy gives exactly the next boundary's entire
auxiliary family. Source: Part II, `con:sweep`, move (4), lines 339–342. -/
theorem rightAuxiliaryUpdate_eq_next (k : Fin (stageCount L w)) :
    Function.update (leftAuxiliaryFrame L w k) (.inl k)
        (rightRetiredAuxiliary L w k) =
      auxiliaryFrameBefore L w (k.val + 1) := by
  funext c
  cases c with
  | inl j =>
      by_cases hj : j = k
      · subst j
        simp [auxiliaryFrameBefore, auxiliaryStage, retiredAuxiliaryFrame]
      · have hv : j.val ≠ k.val := fun h ↦ hj (Fin.ext h)
        rw [Function.update_of_ne (Sum.inl_injective.ne hj)]
        by_cases hlt : j.val < k.val
        · have hnext : j.val < k.val + 1 := by omega
          simp [leftAuxiliaryFrame, auxiliaryFrameBefore, auxiliaryStage, hlt, hnext]
        · have hnext : ¬ j.val < k.val + 1 := by omega
          simp [leftAuxiliaryFrame, auxiliaryFrameBefore, auxiliaryStage, hlt, hnext]
  | inr j =>
      rw [Function.update_of_ne (by simp)]
      have hiff : j.val + 1 < k.val + 1 ↔ j.val + 1 ≤ k.val := by omega
      simp only [leftAuxiliaryFrame, auxiliaryFrameBefore, auxiliaryStage,
        retiredAuxiliaryFrame, hiff]

/-- Every auxiliary occurrence other than the current right copy is unchanged
by its retirement. Source: Part II, `con:sweep`, move (4), lines 339–340. -/
theorem rightAuxiliaryUpdate_spectator (k : Fin (stageCount L w))
    (c : AuxiliaryCopy L w) (hc : c ≠ Sum.inl k) :
    Function.update (leftAuxiliaryFrame L w k) (.inl k)
        (rightRetiredAuxiliary L w k) c = leftAuxiliaryFrame L w k c :=
  Function.update_of_ne hc _ _

/-- Both actual main and auxiliary frame endpoints give the complete next
stage list, including the first stage. This is not a circuit hypothesis.
Source: Part II, `prop:sweep`, proof, lines 375–378. -/
theorem afterRightFrames_eq_sweepFrames (k : Fin (stageCount L w)) :
    afterRightFrames L w k = sweepFrames L w k.succ := by
  obtain ⟨hw, hL⟩ := geometry_of_stageCount_pos ((Nat.zero_le k.val).trans_lt k.isLt)
  rw [afterRightFrames, rightBandMain_eq_stageFrame hw hL k,
    rightAuxiliaryUpdate_eq_next]
  rfl

/-- Selecting a copy occurrence uses its original label, even if frame values
coincide. The other occurrences retain their order.
Source: Part II, `con:sweep`, lines 336–340. -/
theorem sweepFrames_select_auxiliary (k : Fin (stageCount L w + 1))
    (c : AuxiliaryCopy L w) :
    (sweepFrames L w k).Perm
      (auxiliaryFrameBefore L w k.val c :: stageFrame L w k ::
        ((initialAuxiliaryOrder L w).erase c).map (auxiliaryFrameBefore L w k.val)) := by
  have hc : c ∈ initialAuxiliaryOrder L w := by
    simp [initialAuxiliaryOrder]
  simpa only [sweepFrames, List.erase_eq_eraseP, Bool.beq_eq_decide_eq] using
    (perm_map_cons (X := AuxiliaryCopy L w) (stageFrame L w k)
      (l := initialAuxiliaryOrder L w) (x := c) hc
      (auxiliaryFrameBefore L w k.val))

end TNLean.MPS.AreaLaw.ChainSweep
