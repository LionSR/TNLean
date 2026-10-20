/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepFrames

/-!
# Retired auxiliary sheets at their original copy labels

The actual corrected one-band auxiliary sheet is instantiated at each right or
positive-stage left band. The endpoint is the sheet of the existing terminal auxiliary owner,
with the original copy label unchanged.
No circuit, memory trajectory or final auxiliary endpoint is supplied as a hypothesis.

**Local fix (terminal auxiliary registers):** A retired copy retains its A and B strips and
its C-owned exterior. It is not reset to an all-C copy. Integer-ended bands are half-open;
the real exchange window remains open. See
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

Source: the one-dimensional note, Part II, `part2b_mps_protocol.tex`, Construction con:band,
lines 248–276, especially the retained auxiliary registers at lines 271–272; Construction
con:sweep, lines 329–342, and the terminal register distinction in Proposition prop:sweep.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.Lattice

variable {L w : ℕ}

/-- A right copy uses the actual main sheet produced by the preceding left transfer.
Source: Part II, con:sweep, move (4), lines 339–340. -/
def rightRetiredAuxiliary (L w : ℕ)
    (k : Fin (stageCount L w)) : Sheet (Fin L) (Party L w) :=
  OneBand.aux₄ (leftBandMain L w k).owner
    (.inl k.castSucc) (.inl k.succ) (.inr k) ((k.val + 1) * (20 * w)) w

/-- Left copy j is used at stage j+1. Its existence supplies the positive-stage guard;
no left copy or predecessor party is introduced at stage zero.
Source: Part II, con:sweep, move (3), lines 336–338. -/
def leftRetiredAuxiliary (L w : ℕ)
    (j : Fin (stageCount L w - 1)) : Sheet (Fin L) (Party L w) :=
  let k : Fin (stageCount L w) := ⟨j.val + 1, by omega⟩
  OneBand.aux₄ (afterBlockBirth L w k).owner
    (.inl k.castSucc) (.inr k) (.inr ⟨j.val, by omega⟩) ((j.val + 1) * (20 * w)) w

/-- Under the actual left margin, truncated natural subtraction is ordinary integer
subtraction. The comparison concerns the same half-open interval. -/
private theorem mem_interval_nat_sub_iff_int (a u v : ℕ) (hu : u ≤ a) (hv : v ≤ a)
    (x : Fin L) :
    x ∈ interval L (a - u) (a - v) ↔
      (a : ℤ) - u ≤ x.val ∧ (x.val : ℤ) < (a : ℤ) - v := by
  simp only [mem_interval]
  omega

/-- The one-band endpoint in the existing integer coordinate convention. This is a
private comparison lemma, not a second retired-owner definition.
Source: Part II, con:band, lines 271–272, with the half-open correction. -/
private theorem aux₄_eq_raw_integer
    (own : Fin L → Party L w) (A B C : Party L w) (a : ℕ)
    (hw : 1 ≤ w) (hleft : 8 * w ≤ a)
    (hC : ∀ x ∈ interval L (a - 8 * w) a, own x = C) :
    OneBand.aux₄ own A B C a w = Sheet.mk (fun x ↦
      if (a : ℤ) - 3 * w ≤ x.val ∧ (x.val : ℤ) < (a : ℤ) - 2 * w then A
      else if (a : ℤ) - 2 * w ≤ x.val ∧ (x.val : ℤ) < (a : ℤ) - w then B else C) := by
  rw [OneBand.aux₄_eq_raw own A B C a w hw hleft hC]
  apply congrArg (Sheet.mk)
  funext x
  have h32 := mem_interval_nat_sub_iff_int a (3 * w) (2 * w) (by omega) (by omega) x
  have h21 := mem_interval_nat_sub_iff_int a (2 * w) w (by omega) (by omega) x
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h32 h21
  simp only [h32, h21]

/-- The actual right-band auxiliary has precisely its existing right-copy owner.
No desired auxiliary endpoint is assumed. Source: Part II, con:band, lines 271–272,
and con:sweep, move (4), lines 339–340. -/
theorem rightRetiredAuxiliary_eq_raw (hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    rightRetiredAuxiliary L w k =
      Sheet.mk (fun x ↦ auxiliaryOwner L w (Sum.inl k, x)) := by
  have hleft : 8 * w ≤ (k.val + 1) * (20 * w) :=
    stage_left_margin w (k.val + 1) (by omega)
  have hC := (right_band_owners k).1
  change OneBand.aux₄ (leftBandMain L w k).owner
      (.inl k.castSucc) (.inl k.succ) (.inr k) ((k.val + 1) * (20 * w)) w =
    Sheet.mk (fun x ↦
      if (((k.val + 1) * (20 * w) : ℕ) : ℤ) - 3 * w ≤ x.val ∧
          (x.val : ℤ) < (((k.val + 1) * (20 * w) : ℕ) : ℤ) - 2 * w
        then Sum.inl k.castSucc
      else if (((k.val + 1) * (20 * w) : ℕ) : ℤ) - 2 * w ≤ x.val ∧
          (x.val : ℤ) < (((k.val + 1) * (20 * w) : ℕ) : ℤ) - w
        then Sum.inl k.succ else Sum.inr k)
  rw [leftBandMain_eq_afterLeftTransfer hw k]
  exact aux₄_eq_raw_integer _ _ _ _ _ hw hleft hC

/-- The actual positive-stage left-band auxiliary has its original left-copy owner.
The index j labels the copy; its activation stage is j+1. Source: Part II, con:band,
lines 271–272, and con:sweep, move (3), lines 336–338. -/
theorem leftRetiredAuxiliary_eq_raw (hw : 1 ≤ w) (j : Fin (stageCount L w - 1)) :
    leftRetiredAuxiliary L w j =
      Sheet.mk (fun x ↦ auxiliaryOwner L w (Sum.inr j, x)) := by
  let k : Fin (stageCount L w) := ⟨j.val + 1, by omega⟩
  have hk : 0 < k.val := by simp [k]
  have hleft : 8 * w ≤ k.val * (20 * w) := stage_left_margin w k.val (by omega)
  have hC : ∀ x ∈ interval L (k.val * (20 * w) - 8 * w) (k.val * (20 * w)),
      (afterBlockBirth L w k).owner x =
        Sum.inr (⟨j.val, by omega⟩ : Fin (stageCount L w)) := by
    simpa only [k, Nat.add_sub_cancel] using
      (left_band_owners hw k hk).1
  change OneBand.aux₄ (afterBlockBirth L w k).owner
      (.inl k.castSucc) (.inr k) (.inr ⟨j.val, by omega⟩) (k.val * (20 * w)) w =
    Sheet.mk (fun x ↦
      if ((k.val * (20 * w) : ℕ) : ℤ) - 3 * w ≤ x.val ∧
          (x.val : ℤ) < ((k.val * (20 * w) : ℕ) : ℤ) - 2 * w
        then Sum.inl k.castSucc
      else if ((k.val * (20 * w) : ℕ) : ℤ) - 2 * w ≤ x.val ∧
          (x.val : ℤ) < ((k.val * (20 * w) : ℕ) : ℤ) - w
        then Sum.inr k else Sum.inr (⟨j.val, by omega⟩ : Fin (stageCount L w)))
  exact aux₄_eq_raw_integer _ _ _ _ _ hw hleft hC

end TNLean.MPS.AreaLaw.ChainSweep
