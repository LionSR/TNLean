/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepLocalCircuits
import TNLean.Lattice.PartyCircuit.OriginalCircuitLift
import TNLean.Lattice.PartyCircuit.ProtocolDensityError
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The conditional chronological middle sweep

The input is exactly a family of actual local-stage circuits with the
conclusions of the conditional local theorem.
The middle is the existing OriginalCircuit.sequence on Path.operationFrames,
with identity operations after its prescribed last operation. Only derived
layout equalities identify its initial and terminal memories.

Participation and error totals are conclusions, not hypotheses. Counting uses
the existing actual occurrence counts and the fixed stageParticipants sets.
The error proof applies the existing contraction-trajectory theorem. This file
neither supplies the physical information estimates nor initializes the copies,
regroups outputs, compresses the result, or proves the full sweep proposition.

Source: the one-dimensional note, Part II, con:sweep, lines 330–343,
and prop:sweep, lines 349–378.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS.PairEffect.OriginalCircuit

variable {P : Type}

/-- CountTransfer23a099, with noncomputable Set.indicator in the statement.
The only change avoids an undeclared decidability instance; no hypothesis is
added. Source: Part II, prop:sweep, lifetime assertion, lines 353–355. -/
private theorem participationCount_le_indicator
    {a b : Layout P} {c : OriginalCircuit a b} {S : Set P}
    {r K : ℕ} {ε : ℝ} {x : Mem a} {y : Mem b}
    (h : c.IsBoundedChange S r K ε x y) (p : P) :
    c.participationCount p ≤ S.indicator (fun _ ↦ (1 : ℕ)) p := by
  classical
  by_cases hp : p ∈ S
  · rw [Set.indicator_of_mem hp]
    calc
      c.participationCount p ≤ Nat.card c.nonprivateLocations :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = c.nonprivateCount := c.natCard_nonprivateLocations
      _ ≤ 1 := h.nonprivateCount_le
  · rw [Set.indicator_of_notMem hp]
    have hzero : c.participationCount p = 0 := by
      exact Nat.card_eq_zero.mpr
        (Or.inl ⟨fun g ↦ hp (h.participants_subset g.1 g.2)⟩)
    exact hzero.le

/-- CountTransfer23a099 on the actual existing chronological sequence.
Source: Part II, prop:sweep, lifetime assertion, lines 353–355. -/
private theorem participationCount_sequence_le_indicators
    (a : ℕ → Layout P) (step : (s : ℕ) → OriginalCircuit (a s) (a (s + 1)))
    {S : ℕ → Set P} {r K : ℕ → ℕ} {ε : ℕ → ℝ}
    {x : (s : ℕ) → Mem (a s)} {y : (s : ℕ) → Mem (a (s + 1))}
    (t : ℕ)
    (hstep : ∀ s < t, (step s).IsBoundedChange (S s) (r s) (K s) (ε s) (x s) (y s))
    (p : P) :
    (sequence a step t).participationCount p ≤
      ∑ s ∈ Finset.range t, (S s).indicator (fun _ ↦ (1 : ℕ)) p := by
  classical
  rw [participationCount_sequence]
  exact Finset.sum_le_sum fun s hs ↦
    participationCount_le_indicator (hstep s (Finset.mem_range.mp hs)) p

/-- Equality transport of the existing participation count adds no occurrence.
Source: Part II, prop:sweep, lines 353–355. -/
private theorem participationCount_castLayouts {a b a' b' : Layout P}
    (c : OriginalCircuit a b) (ha : a = a') (hb : b = b') (p : P) :
    (c.castLayouts ha hb).participationCount p = c.participationCount p := by
  cases ha
  cases hb
  rfl

/-- Equality transport retains an actual identity circuit.
Source: the scalar and register-list identifications in Part II, con:sweep. -/
private theorem castLayouts_id_heq {a b a' b' : Layout P}
    (c : OriginalCircuit a b) (ha : a = a') (hb : b = b')
    (h : HEq c (OriginalCircuit.id a)) :
    HEq (c.castLayouts ha hb) (OriginalCircuit.id a') := by
  cases ha
  cases hb
  exact h

end TNLean.PEPS.PairEffect.OriginalCircuit

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.PEPS.PairEffect TNLean.PEPS.EncodedFrame

variable {L w q : ℕ}

/-- The existing Mathlib finite-product equivalence, in Path's chronological
order. Source: Part II, con:sweep, lines 330–343. -/
private def middleSlotEquiv (L w : ℕ) :
    Fin (sweepOperationCount L w) ≃ Fin (stageCount L w) × Fin 18 :=
  (finCongr (by simp [sweepOperationCount, Nat.mul_comm])).trans finProdFinEquiv.symm

private theorem middleSlotEquiv_inverse_val (k : Fin (stageCount L w)) (j : Fin 18) :
    ((middleSlotEquiv L w).symm (k, j)).val = 18 * k.val + j.val := by
  change j.val + 18 * k.val = 18 * k.val + j.val
  omega

private theorem middleSlotEquiv_recompose (n : Fin (sweepOperationCount L w)) :
    18 * ((middleSlotEquiv L w n).1).val + ((middleSlotEquiv L w n).2).val = n.val := by
  calc
    _ = ((middleSlotEquiv L w).symm (middleSlotEquiv L w n)).val :=
      (middleSlotEquiv_inverse_val (middleSlotEquiv L w n).1
        (middleSlotEquiv L w n).2).symm
    _ = n.val := congrArg Fin.val ((middleSlotEquiv L w).symm_apply_apply n)

/-- This is precisely the existing Path boundary identity at the selected
stage and slot, including its final slot. Source: Part II, prop:sweep, lines 375–378. -/
private theorem middleSlot_boundaries (n : Fin (sweepOperationCount L w)) :
    operationFrames L w n.val = stageBoundaryFrames L w
        (middleSlotEquiv L w n).1 (middleSlotEquiv L w n).2.val ∧
      operationFrames L w (n.val + 1) = stageBoundaryFrames L w
        (middleSlotEquiv L w n).1 ((middleSlotEquiv L w n).2.val + 1) := by
  have h := operationFrames_step (q := q)
    (middleSlotEquiv L w n).1 (middleSlotEquiv L w n).2
  simpa only [middleSlotEquiv_recompose] using h

private abbrev middleLayout (n : ℕ) : Layout (Party L w) :=
  stackRegs (operationFrames L w n) []

/-- Only a reindexing of the existing prescribed participant sets; after the
last actual operation the allowed set is empty. Source: Part II, con:sweep. -/
private def middleParticipants (L w : ℕ) (n : ℕ) : Set (Party L w) :=
  if hn : n < sweepOperationCount L w then
    stageParticipants (middleSlotEquiv L w ⟨n, hn⟩).1 (middleSlotEquiv L w ⟨n, hn⟩).2
  else ∅

variable (c : (k : Fin (stageCount L w)) → (j : Fin 18) → OriginalCircuit
  (stackRegs (stageBoundaryFrames L w k j.val) [])
  (stackRegs (stageBoundaryFrames L w k (j.val + 1)) []))

/-- Extend the exact local family on the already defined operationFrames.
The tail is an identity; casts use only Path's derived frame equalities.
Source: Part II, con:sweep, lines 330–343. -/
def sweepMiddleStep (n : ℕ) : OriginalCircuit
    (middleLayout (L := L) (w := w) (q := q) n)
    (middleLayout (L := L) (w := w) (q := q) (n + 1)) :=
  if hn : n < sweepOperationCount L w then
    (c (middleSlotEquiv L w ⟨n, hn⟩).1 (middleSlotEquiv L w ⟨n, hn⟩).2).castLayouts
      (congrArg (fun Fs ↦ stackRegs Fs [])
        (middleSlot_boundaries (q := q) ⟨n, hn⟩).1.symm)
      (congrArg (fun Fs ↦ stackRegs Fs [])
        (middleSlot_boundaries (q := q) ⟨n, hn⟩).2.symm)
  else
    (OriginalCircuit.id (middleLayout (L := L) (w := w) (q := q) n)).castLayouts rfl
      (congrArg (fun Fs ↦ stackRegs Fs [])
        ((operationFrames_of_le (q := q)
          (by omega : sweepOperationCount L w ≤ n)).trans
          (operationFrames_of_le (q := q)
            (by omega : sweepOperationCount L w ≤ n + 1)).symm))

/-- The middle is the existing chronological sequence, with its proven initial
and terminal frame lists. No trajectory or endpoint is supplied.
Source: Part II, prop:sweep, lines 365–378. -/
def sweepMiddleCircuit : OriginalCircuit
    (stackRegs (initialFrames L w) []) (stackRegs (terminalFrames L w) []) :=
  (OriginalCircuit.sequence
    (middleLayout (L := L) (w := w) (q := q)) (sweepMiddleStep c)
    (sweepOperationCount L w)).castLayouts
      (congrArg (fun Fs ↦ stackRegs Fs []) (operationFrames_zero L w))
      (congrArg (fun Fs ↦ stackRegs Fs []) (operationFrames_last (L := L) (w := w)
        (q := q)))

variable [NeZero q]

private theorem castFrames_bounded {F G F' G' : List (Sheet (Fin L) (Party L w))}
    (d : OriginalCircuit (stackRegs F []) (stackRegs G [])) (hF : F = F') (hG : G = G')
    {S : Set (Party L w)} {r K : ℕ} {ε : ℝ} (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (h : d.IsBoundedChange S r K ε (framesVec Ω F) (framesVec Ω G)) :
    (d.castLayouts (congrArg (fun Fs ↦ stackRegs Fs []) hF)
      (congrArg (fun Fs ↦ stackRegs Fs []) hG)).IsBoundedChange S r K ε
        (framesVec Ω F') (framesVec Ω G') := by
  cases hF
  cases hG
  exact h

private theorem castFrames_error {F G F' G' : List (Sheet (Fin L) (Party L w))}
    (d : OriginalCircuit (stackRegs F []) (stackRegs G [])) (hF : F = F') (hG : G = G')
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    ‖(d.castLayouts (congrArg (fun Fs ↦ stackRegs Fs []) hF)
        (congrArg (fun Fs ↦ stackRegs Fs []) hG)).eval (framesVec Ω F') - framesVec Ω G'‖ =
      ‖d.eval (framesVec Ω F) - framesVec Ω G‖ := by
  cases hF
  cases hG
  rfl

variable (Ω : EuclideanSpace ℂ (Fin L → Fin q))

/- Exactly the conclusion of the existing conditional local-stage theorem,
now for every actual stage. These local circuits are the sole conditional
construction input; no total participation or trajectory is supplied. -/
variable (hc : ∀ k j, (c k j).IsBoundedChange (stageParticipants k j) 1 1
    (4 * (L : ℝ) ^ (-12 : ℤ))
    (framesVec Ω (stageBoundaryFrames L w k j.val))
    (framesVec Ω (stageBoundaryFrames L w k (j.val + 1))) ∧
  (c k j).IsSourceBounded 1 ∧ (c k j).nonprivateCount ≤ 1 ∧
  ((k.val = 0 ∧ 3 ≤ j.val ∧ j.val < 10) → (c k j).nonprivateCount = 0 ∧
    ‖(c k j).eval (framesVec Ω (stageBoundaryFrames L w k j.val)) -
      framesVec Ω (stageBoundaryFrames L w k (j.val + 1))‖ = 0 ∧
    HEq (c k j) (OriginalCircuit.id (stackRegs (stageBoundaryFrames L w k j.val) []))))

include hc

/-- Every actual operation retains its exact local bounds, and every tail
operation is an identity with zero reference error. Source: Part II, prop:sweep. -/
private theorem middleStep_bounded (n : ℕ) :
    (sweepMiddleStep c n).IsBoundedChange (middleParticipants L w n) 1 1
      (if n < sweepOperationCount L w then 4 * (L : ℝ) ^ (-12 : ℤ) else 0)
      (framesVec Ω (operationFrames L w n))
      (framesVec Ω (operationFrames L w (n + 1))) := by
  classical
  by_cases hn : n < sweepOperationCount L w
  · simp only [sweepMiddleStep, middleParticipants, dite_eq_left hn, ite_eq_left hn]
    exact castFrames_bounded _
      (middleSlot_boundaries (q := q) ⟨n, hn⟩).1.symm
      (middleSlot_boundaries (q := q) ⟨n, hn⟩).2.symm Ω (hc _ _).1
  · simp only [sweepMiddleStep, middleParticipants, dite_eq_right hn, ite_eq_right hn]
    exact castFrames_bounded _ rfl
      ((operationFrames_of_le (q := q) (Nat.le_of_not_gt hn)).trans
        (operationFrames_of_le (q := q)
          (by omega : sweepOperationCount L w ≤ n + 1)).symm) Ω
      (OriginalCircuit.isBoundedChange_id ∅ 1 1 le_rfl _)

private theorem middleStep_sourceBounded (n : ℕ) : (sweepMiddleStep c n).IsSourceBounded 1 := by
  classical
  by_cases hn : n < sweepOperationCount L w
  · simp only [sweepMiddleStep, dite_eq_left hn]
    exact OriginalCircuit.isSourceBounded_castLayouts _ _ _ (hc _ _).2.1
  · simp only [sweepMiddleStep, dite_eq_right hn]
    exact OriginalCircuit.isSourceBounded_castLayouts _ _ _ trivial

omit hc [NeZero q] in
/-- No additional operation is introduced beyond the fixed Path length.
Source: Part II, con:sweep, end of the stage loop. -/
theorem sweepMiddleStep_tail_identity (n : ℕ) (hn : sweepOperationCount L w ≤ n) :
    HEq (sweepMiddleStep c n)
      (OriginalCircuit.id (middleLayout (L := L) (w := w) (q := q) n)) := by
  simp only [sweepMiddleStep, dite_eq_right (not_lt.mpr hn)]
  exact OriginalCircuit.castLayouts_id_heq _ _ _ HEq.rfl

/-- The seven existing first-stage padding slots remain actual identities.
Source: Part II, con:sweep, exceptional left transfer, lines 337–338. -/
theorem sweepMiddleStep_first_padding (k : Fin (stageCount L w)) (j : Fin 18)
    (hk : k.val = 0) (hj : 3 ≤ j.val ∧ j.val < 10) :
    HEq (sweepMiddleStep c (18 * k.val + j.val))
      (OriginalCircuit.id (middleLayout (L := L) (w := w) (q := q)
        (18 * k.val + j.val))) := by
  have hn : 18 * k.val + j.val < sweepOperationCount L w := by
    have hki := k.isLt
    have hji := j.isLt
    unfold sweepOperationCount
    omega
  let n : Fin (sweepOperationCount L w) := ⟨18 * k.val + j.val, hn⟩
  have he : middleSlotEquiv L w n = (k, j) := by
    apply (middleSlotEquiv L w).symm.injective
    rw [Equiv.symm_apply_apply]
    apply Fin.ext
    exact (middleSlotEquiv_inverse_val k j).symm
  simp only [sweepMiddleStep, dite_eq_left hn]
  have hid := (hc k j).2.2.2 ⟨hk, hj.1, hj.2⟩
  have hid' : HEq (c (middleSlotEquiv L w n).1 (middleSlotEquiv L w n).2)
      (OriginalCircuit.id (stackRegs (stageBoundaryFrames L w
        (middleSlotEquiv L w n).1 (middleSlotEquiv L w n).2.val) [])) := by
    rw [he]
    exact hid.2.2
  exact OriginalCircuit.castLayouts_id_heq _ _ _ hid'

omit hc in
/-- The range sum is the already defined stage-slot incidence count, using
Mathlib's finite-product equivalence rather than a second counting model.
Source: Part II, prop:sweep, lifetime assertion, lines 353–355. -/
private theorem middleIndicators_eq_scheduled (p : Party L w) :
    (∑ n ∈ Finset.range (sweepOperationCount L w),
      (middleParticipants L w n).indicator (fun _ ↦ (1 : ℕ)) p) =
        scheduledParticipationCount p := by
  classical
  rw [← Fin.sum_univ_eq_sum_range
    (fun n ↦ (middleParticipants L w n).indicator (fun _ ↦ (1 : ℕ)) p)]
  calc
    _ = ∑ e : Fin (stageCount L w) × Fin 18,
        if p ∈ stageParticipants e.1 e.2 then 1 else 0 := by
      apply Fintype.sum_equiv (middleSlotEquiv L w)
      intro n
      simp only [middleParticipants, dite_eq_left n.isLt, Set.indicator_apply]
    _ = scheduledParticipationCount p := by
      simp only [scheduledParticipationCount, stageOccurrences, Finset.sum_boole, Nat.cast_id]

/-- The actual chronological middle circuit has the derived lifetime bound 40.
No total participation premise is used. Source: Part II, prop:sweep, lines 353–355. -/
theorem sweepMiddleCircuit_participation_le_forty (p : Party L w) :
    (sweepMiddleCircuit c).participationCount p ≤ 40 := by
  unfold sweepMiddleCircuit
  rw [OriginalCircuit.participationCount_castLayouts]
  exact (OriginalCircuit.participationCount_sequence_le_indicators
    (middleLayout (L := L) (w := w) (q := q)) (sweepMiddleStep c)
    (sweepOperationCount L w) (fun n _ ↦ middleStep_bounded c Ω hc n) p).trans
      ((middleIndicators_eq_scheduled (L := L) (w := w) p).le.trans
        (scheduledParticipationCount_le_forty p))

/-- The actual global nonprivate count is bounded by the fixed number of
primitive slots. Source: Part II, prop:sweep, lines 353–355. -/
theorem sweepMiddleCircuit_nonprivateCount_le :
    (sweepMiddleCircuit c).nonprivateCount ≤ sweepOperationCount L w := by
  unfold sweepMiddleCircuit
  rw [OriginalCircuit.nonprivateCount_castLayouts, OriginalCircuit.nonprivateCount_sequence]
  calc
    _ ≤ ∑ _n ∈ Finset.range (sweepOperationCount L w), 1 :=
      Finset.sum_le_sum fun n _ ↦ (middleStep_bounded c Ω hc n).nonprivateCount_le
    _ = _ := by simp

private theorem middleSequence_sourceBounded (n : ℕ) :
    (OriginalCircuit.sequence (middleLayout (L := L) (w := w) (q := q))
      (sweepMiddleStep c) n).IsSourceBounded 1 := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih, middleStep_sourceBounded c Ω hc n⟩

/-- Per-monomial pair sources, effects and expansion bounds are those of the
actual constituent circuits. Source: Part II, prop:sweep, lines 353–355. -/
theorem sweepMiddleCircuit_resource_bounds :
    (sweepMiddleCircuit c).IsSourceBounded 1 ∧
      (sweepMiddleCircuit c).IsExpansionBounded 1 1 ∧
      (sweepMiddleCircuit c).IsMonomialBounded 1 := by
  unfold sweepMiddleCircuit
  refine ⟨OriginalCircuit.isSourceBounded_castLayouts _ _ _
      (middleSequence_sourceBounded c Ω hc _),
    OriginalCircuit.isExpansionBounded_castLayouts _ _ _ ?_,
    OriginalCircuit.isMonomialBounded_castLayouts _ _ _ ?_⟩
  · exact OriginalCircuit.isExpansionBounded_sequence _ _ 1 1 _
      (fun n _ ↦ by simpa only [Nat.cast_one] using
        (middleStep_bounded c Ω hc n).isExpansionBounded)
  · exact OriginalCircuit.isMonomialBounded_sequence _ _ 1 _
      (fun n _ ↦ (middleStep_bounded c Ω hc n).isMonomialBounded)

/-- The actual middle output is subnormalized and its vector error is the
sum-bound obtained from the existing contraction-trajectory theorem.
No actual output, error or trajectory is supplied as a hypothesis.
Source: Part II, prop:sweep, vector error assertion, lines 355–359. -/
theorem sweepMiddleCircuit_norm_and_error (hΩ : ‖Ω‖ = 1) :
    ‖(sweepMiddleCircuit c).eval (framesVec Ω (initialFrames L w))‖ ≤ 1 ∧
      ‖(sweepMiddleCircuit c).eval (framesVec Ω (initialFrames L w)) -
          framesVec Ω (terminalFrames L w)‖ ≤
        (sweepOperationCount L w : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ)) := by
  have hnorm : ‖(sweepMiddleCircuit c).eval (framesVec Ω (initialFrames L w))‖ ≤ 1 :=
    ((sweepMiddleCircuit c).norm_eval_le_norm _).trans (norm_initialFrames hΩ).le
  refine ⟨hnorm, ?_⟩
  let a := middleLayout (L := L) (w := w) (q := q)
  let step := sweepMiddleStep c
  let N := sweepOperationCount L w
  let ref : (n : ℕ) → Mem (a n) := fun n ↦ framesVec Ω (operationFrames L w n)
  let x : (n : ℕ) → Mem (a n) := fun n ↦
    (OriginalCircuit.sequence a step n).eval (ref 0)
  let S : (n : ℕ) → Mem (a n) →ₗ[ℂ] Mem (a (n + 1)) := fun n ↦ (step n).eval.toLinearMap
  have herr : ‖x N - ref N‖ ≤ ∑ n ∈ Finset.range N, ‖S n (ref n) - ref (n + 1)‖ :=
    TNLean.PEPS.Approximation.norm_trajectory_sub_reference_le S x ref N
      (fun n _ v ↦ (step n).norm_eval_le_norm v) rfl
      (fun n _ ↦ OriginalCircuit.eval_sequence_succ a step n (ref 0))
  have herr' : ‖x N - ref N‖ ≤ (N : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    refine herr.trans ?_
    calc
      _ ≤ ∑ _n ∈ Finset.range N, 4 * (L : ℝ) ^ (-12 : ℤ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hb := (middleStep_bounded c Ω hc n).norm_eval_sub_le
        have hn' : n < sweepOperationCount L w := Finset.mem_range.mp hn
        simpa only [S, step, ref, ContinuousLinearMap.coe_coe, ite_eq_left hn'] using hb
      _ = _ := by simp
  unfold sweepMiddleCircuit
  rw [castFrames_error _ (operationFrames_zero L w)
    (operationFrames_last (L := L) (w := w) (q := q)) Ω]
  exact herr'

end TNLean.MPS.AreaLaw.ChainSweep
