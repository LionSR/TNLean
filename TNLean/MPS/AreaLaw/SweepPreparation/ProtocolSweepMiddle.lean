/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolSweepLocalCircuits
import TNLean.Algebra.ProtocolDensityError
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The conditional chronological middle sweep

The input is exactly a family of actual local-stage circuits with the
conclusions of the conditional local theorem.
The middle is the existing OriginalCircuit.sequence on Path.operationFrames,
with empty operations after its prescribed last operation. Only derived
equalities of sheet lists identify its initial and terminal systems; they enter
as identifications of the bases (`OriginalCircuit.castSystems`), which add no gate.

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

namespace TNLean.MPS.AreaLaw.ChainSweep

open Matrix QuantumCircuit.Party
open ManyBody (Config)

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
  have h := operationFrames_step
    (middleSlotEquiv L w n).1 (middleSlotEquiv L w n).2
  simpa only [middleSlotEquiv_recompose] using h

/-- A circuit with at most one nonprivate gate, whose participants lie in `S`, involves a
party at most once, and only a party of `S`.
Source: Part II, prop:sweep, lifetime assertion, lines 353–355. -/
private theorem participation_le_indicator {P : Type} [DecidableEq P] {X Y : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [Fintype P] [∀ p, Fintype (Y p)]
    {c : OriginalCircuit X Y} {S : Set P} {r K : ℕ} {ε : ℝ}
    {x : EuclideanSpace ℂ (Config X)} {y : EuclideanSpace ℂ (Config Y)}
    (h : c.IsBoundedChange S r K ε x y) (p : P) :
    c.participation p ≤ S.indicator (fun _ ↦ (1 : ℕ)) p := by
  classical
  rw [← c.natCard_participants_mem]
  by_cases hp : p ∈ S
  · rw [Set.indicator_of_mem hp]
    calc
      Nat.card {g : c.nonprivateLocations // p ∈ c.participants g} ≤
          Nat.card c.nonprivateLocations :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = c.nonprivateCount := c.natCard_nonprivateLocations
      _ ≤ 1 := h.nonprivateCount_le
  · rw [Set.indicator_of_notMem hp]
    exact (Nat.card_eq_zero.mpr
      (Or.inl ⟨fun g ↦ hp (h.participants_subset g.1 g.2)⟩)).le

/-- Identifying the systems keeps a bounded change, read on the identified vectors. -/
private theorem isBoundedChange_castSystems {P : Type} [DecidableEq P] [Fintype P]
    {X Y X' Y' : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] [∀ p, Fintype (X' p)]
    [∀ p, DecidableEq (X' p)] [∀ p, Fintype (Y' p)] [∀ p, DecidableEq (Y' p)]
    {c : OriginalCircuit X Y} {S : Set P} {r K : ℕ} {ε : ℝ}
    {x : EuclideanSpace ℂ (Config X)} {y : EuclideanSpace ℂ (Config Y)}
    (h : c.IsBoundedChange S r K ε x y) (hX : X = X') (hY : Y = Y') :
    (c.castSystems hX hY).IsBoundedChange S r K ε (OriginalCircuit.castVector hX x)
      (OriginalCircuit.castVector hY y) where
  nonprivateCount_le := by
    rw [OriginalCircuit.nonprivateCount_castSystems]
    exact h.nonprivateCount_le
  participants_subset := OriginalCircuit.forall_participants_castSystems
    (Q := fun D ↦ (↑D : Set P) ⊆ S) c hX hY h.participants_subset
  isExpansionBounded := (c.isExpansionBounded_castSystems hX hY).mpr h.isExpansionBounded
  isMonomialBounded := (c.isMonomialBounded_castSystems hX hY).mpr h.isMonomialBounded
  norm_op_sub_le := by
    rw [OriginalCircuit.norm_toEuclideanLin_op_castSystems_sub]
    exact h.norm_op_sub_le

/-- The system of the sheets after the first `n` operations. -/
private abbrev middleSystem (n : ℕ) : Party L w → Type :=
  stackSystem (Sheet.system q) (operationFrames L w n) fun _ ↦ Unit

/-- Only a reindexing of the existing prescribed participant sets; after the
last actual operation the allowed set is empty. Source: Part II, con:sweep. -/
private def middleParticipants (L w : ℕ) (n : ℕ) : Set (Party L w) :=
  if hn : n < sweepOperationCount L w then
    stageParticipants (middleSlotEquiv L w ⟨n, hn⟩).1 (middleSlotEquiv L w ⟨n, hn⟩).2
  else ∅

variable (c : (k : Fin (stageCount L w)) → (j : Fin 18) → OriginalCircuit
  (stackSystem (Sheet.system q) (stageBoundaryFrames L w k j.val) fun _ ↦ Unit)
  (stackSystem (Sheet.system q) (stageBoundaryFrames L w k (j.val + 1)) fun _ ↦ Unit))

/-- Extend the exact local family on the already defined operationFrames.
The tail is the empty circuit; the identifications use only Path's derived sheet equalities.
Source: Part II, con:sweep, lines 330–343. -/
def sweepMiddleStep (n : ℕ) : OriginalCircuit
    (middleSystem (L := L) (w := w) (q := q) n)
    (middleSystem (L := L) (w := w) (q := q) (n + 1)) :=
  if hn : n < sweepOperationCount L w then
    (c (middleSlotEquiv L w ⟨n, hn⟩).1 (middleSlotEquiv L w ⟨n, hn⟩).2).castSystems
      (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit)
        (middleSlot_boundaries ⟨n, hn⟩).1.symm)
      (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit)
        (middleSlot_boundaries ⟨n, hn⟩).2.symm)
  else
    (OriginalCircuit.done (middleSystem (L := L) (w := w) (q := q) n)).castSystems rfl
      (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit)
        ((operationFrames_of_le
          (by omega : sweepOperationCount L w ≤ n)).trans
          (operationFrames_of_le
            (by omega : sweepOperationCount L w ≤ n + 1)).symm))

/-- The middle is the existing chronological sequence, with its proven initial
and terminal sheet lists. No trajectory or endpoint is supplied.
Source: Part II, prop:sweep, lines 365–378. -/
def sweepMiddleCircuit : OriginalCircuit
    (stackSystem (Sheet.system q) (initialFrames L w) fun _ ↦ Unit)
    (stackSystem (Sheet.system q) (terminalFrames L w) fun _ ↦ Unit) :=
  (OriginalCircuit.sequence
    (middleSystem (L := L) (w := w) (q := q)) (sweepMiddleStep c)
    (sweepOperationCount L w)).castSystems
      (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit)
        (operationFrames_zero L w))
      (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit)
        (operationFrames_last (L := L) (w := w)))

/-- The reference vector of a list of sheets, read on an equal list. -/
private theorem castVector_framesVec {F F' : List (Sheet (Fin L) (Party L w))} (hF : F = F')
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    OriginalCircuit.castVector (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit)
        hF) (framesVec (fun S ↦ S.refVec Ω) F) = framesVec (fun S ↦ S.refVec Ω) F' := by
  subst hF
  rfl

private theorem castFrames_bounded {F G F' G' : List (Sheet (Fin L) (Party L w))}
    (d : OriginalCircuit (stackSystem (Sheet.system q) F fun _ ↦ Unit)
      (stackSystem (Sheet.system q) G fun _ ↦ Unit))
    (hF : F = F') (hG : G = G')
    {S : Set (Party L w)} {r K : ℕ} {ε : ℝ} (Ω : EuclideanSpace ℂ (Fin L → Fin q))
    (h : d.IsBoundedChange S r K ε (framesVec (fun S ↦ S.refVec Ω) F)
      (framesVec (fun S ↦ S.refVec Ω) G)) :
    (d.castSystems (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit) hF)
      (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit) hG)).IsBoundedChange
        S r K ε (framesVec (fun S ↦ S.refVec Ω) F') (framesVec (fun S ↦ S.refVec Ω) G') := by
  have h' := isBoundedChange_castSystems h
    (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit) hF)
    (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit) hG)
  rwa [castVector_framesVec hF, castVector_framesVec hG] at h'

private theorem castFrames_error {F G F' G' : List (Sheet (Fin L) (Party L w))}
    (d : OriginalCircuit (stackSystem (Sheet.system q) F fun _ ↦ Unit)
      (stackSystem (Sheet.system q) G fun _ ↦ Unit))
    (hF : F = F') (hG : G = G') (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    ‖toEuclideanLin (d.castSystems
        (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit) hF)
        (congrArg (fun Fs ↦ stackSystem (Sheet.system q) Fs fun _ ↦ Unit) hG)).op
          (framesVec (fun S ↦ S.refVec Ω) F') - framesVec (fun S ↦ S.refVec Ω) G'‖ =
      ‖toEuclideanLin d.op (framesVec (fun S ↦ S.refVec Ω) F) -
        framesVec (fun S ↦ S.refVec Ω) G‖ := by
  rw [← castVector_framesVec hF, ← castVector_framesVec hG,
    OriginalCircuit.norm_toEuclideanLin_op_castSystems_sub]

variable (Ω : EuclideanSpace ℂ (Fin L → Fin q))

/- Exactly the conclusion of the existing conditional local-stage theorem,
now for every actual stage. These local circuits are the sole conditional
construction input; no total participation or trajectory is supplied. -/
variable (hc : ∀ k j, (c k j).IsBoundedChange (stageParticipants k j) 1 1
    (4 * (L : ℝ) ^ (-12 : ℤ))
    (framesVec (fun S ↦ S.refVec Ω) (stageBoundaryFrames L w k j.val))
    (framesVec (fun S ↦ S.refVec Ω) (stageBoundaryFrames L w k (j.val + 1))) ∧
  (c k j).IsSourceBounded 1 ∧ (c k j).nonprivateCount ≤ 1 ∧
  ((k.val = 0 ∧ 3 ≤ j.val ∧ j.val < 10) → (c k j).nonprivateCount = 0 ∧
    ‖toEuclideanLin (c k j).op
        (framesVec (fun S ↦ S.refVec Ω) (stageBoundaryFrames L w k j.val)) -
      framesVec (fun S ↦ S.refVec Ω) (stageBoundaryFrames L w k (j.val + 1))‖ = 0 ∧
    (c k j).toPartyCircuit.IsLocal))

include hc

/-- Every actual operation retains its exact local bounds, and every tail
operation is empty with zero reference error. Source: Part II, prop:sweep. -/
private theorem middleStep_bounded (n : ℕ) :
    (sweepMiddleStep c n).IsBoundedChange (middleParticipants L w n) 1 1
      (if n < sweepOperationCount L w then 4 * (L : ℝ) ^ (-12 : ℤ) else 0)
      (framesVec (fun S ↦ S.refVec Ω) (operationFrames L w n))
      (framesVec (fun S ↦ S.refVec Ω) (operationFrames L w (n + 1))) := by
  classical
  by_cases hn : n < sweepOperationCount L w
  · simp only [sweepMiddleStep, middleParticipants, dite_eq_left hn, ite_eq_left hn]
    exact castFrames_bounded _
      (middleSlot_boundaries ⟨n, hn⟩).1.symm
      (middleSlot_boundaries ⟨n, hn⟩).2.symm Ω (hc _ _).1
  · simp only [sweepMiddleStep, middleParticipants, dite_eq_right hn, ite_eq_right hn]
    have h0 : (OriginalCircuit.done (middleSystem (L := L) (w := w) (q := q) n)).IsBoundedChange
        ∅ 1 1 0 (framesVec (fun S ↦ S.refVec Ω) (operationFrames L w n))
          (framesVec (fun S ↦ S.refVec Ω) (operationFrames L w n)) := by
      simpa only [OriginalCircuit.op_done, Matrix.toEuclideanLin_one_apply] using
        OriginalCircuit.isBoundedChange_of_nonprivateCount_eq_zero
          (c := OriginalCircuit.done (middleSystem (L := L) (w := w) (q := q) n)) rfl ∅ 1 1
          le_rfl (framesVec (fun S ↦ S.refVec Ω) (operationFrames L w n))
    exact castFrames_bounded _ rfl
      ((operationFrames_of_le (Nat.le_of_not_gt hn)).trans
        (operationFrames_of_le
          (by omega : sweepOperationCount L w ≤ n + 1)).symm) Ω h0

private theorem middleStep_sourceBounded (n : ℕ) :
    (sweepMiddleStep c n).IsSourceBounded 1 := by
  classical
  by_cases hn : n < sweepOperationCount L w
  · simp only [sweepMiddleStep, dite_eq_left hn]
    exact (OriginalCircuit.isSourceBounded_castSystems _ _ _).mpr (hc _ _).2.1
  · simp only [sweepMiddleStep, dite_eq_right hn]
    exact (OriginalCircuit.isSourceBounded_castSystems _ _ _).mpr
      (OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero rfl 1)

omit hc in
/-- No additional gate is introduced beyond the fixed Path length.
Source: Part II, con:sweep, end of the stage loop. -/
theorem sweepMiddleStep_tail_isLocal (n : ℕ) (hn : sweepOperationCount L w ≤ n) :
    (sweepMiddleStep (q := q) c n).toPartyCircuit.IsLocal := by
  simp only [sweepMiddleStep, dite_eq_right (not_lt.mpr hn)]
  exact (OriginalCircuit.isLocal_castSystems_iff _ _ _).mpr trivial

/-- The seven existing first-stage padding slots have no gate.
Source: Part II, con:sweep, exceptional left transfer, lines 337–338. -/
theorem sweepMiddleStep_first_padding_isLocal (k : Fin (stageCount L w)) (j : Fin 18)
    (hk : k.val = 0) (hj : 3 ≤ j.val ∧ j.val < 10) :
    (sweepMiddleStep c (18 * k.val + j.val)).toPartyCircuit.IsLocal := by
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
  have hid' : (c (middleSlotEquiv L w n).1 (middleSlotEquiv L w n).2).toPartyCircuit.IsLocal := by
    rw [he]
    exact hid.2.2
  exact (OriginalCircuit.isLocal_castSystems_iff _ _ _).mpr hid'

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
    (sweepMiddleCircuit c).participation p ≤ 40 := by
  unfold sweepMiddleCircuit
  rw [OriginalCircuit.participation_castSystems, OriginalCircuit.participation_sequence]
  exact (Finset.sum_le_sum fun n _ ↦ participation_le_indicator
    (middleStep_bounded c Ω hc n) p).trans
      ((middleIndicators_eq_scheduled (L := L) (w := w) p).le.trans
        (scheduledParticipationCount_le_forty p))

/-- The actual global nonprivate count is bounded by the fixed number of
primitive slots. Source: Part II, prop:sweep, lines 353–355. -/
theorem sweepMiddleCircuit_nonprivateCount_le :
    (sweepMiddleCircuit c).nonprivateCount ≤ sweepOperationCount L w := by
  unfold sweepMiddleCircuit
  simp only [OriginalCircuit.nonprivateCount_castSystems, OriginalCircuit.nonprivateCount_sequence]
  calc
    _ ≤ ∑ _n ∈ Finset.range (sweepOperationCount L w), 1 :=
      Finset.sum_le_sum fun n _ ↦ (middleStep_bounded c Ω hc n).nonprivateCount_le
    _ = _ := by simp

/-- Per-monomial pair sources, effects and expansion bounds are those of the
actual constituent circuits. Source: Part II, prop:sweep, lines 353–355. -/
theorem sweepMiddleCircuit_resource_bounds :
    (sweepMiddleCircuit c).IsSourceBounded 1 ∧
      (sweepMiddleCircuit c).IsExpansionBounded 1 1 ∧
      (sweepMiddleCircuit c).IsMonomialBounded 1 := by
  unfold sweepMiddleCircuit
  refine ⟨(OriginalCircuit.isSourceBounded_castSystems _ _ _).mpr
      (OriginalCircuit.isSourceBounded_sequence _ _ 1 _
        fun n _ ↦ middleStep_sourceBounded c Ω hc n),
    (OriginalCircuit.isExpansionBounded_castSystems _ _ _).mpr
      (OriginalCircuit.isExpansionBounded_sequence _ _ 1 1 _ fun n _ ↦ by
        simpa only [Nat.cast_one] using (middleStep_bounded c Ω hc n).isExpansionBounded),
    (OriginalCircuit.isMonomialBounded_castSystems _ _ _).mpr
      (OriginalCircuit.isMonomialBounded_sequence _ _ 1 _
        fun n _ ↦ (middleStep_bounded c Ω hc n).isMonomialBounded)⟩

/-- The actual middle output is subnormalized and its vector error is the
sum-bound obtained from the existing contraction-trajectory theorem.
No actual output, error or trajectory is supplied as a hypothesis.
Source: Part II, prop:sweep, vector error assertion, lines 355–359. -/
theorem sweepMiddleCircuit_norm_and_error (hΩ : ‖Ω‖ = 1) :
    ‖toEuclideanLin (sweepMiddleCircuit c).op
        (framesVec (fun S ↦ S.refVec Ω) (initialFrames L w))‖ ≤ 1 ∧
      ‖toEuclideanLin (sweepMiddleCircuit c).op
          (framesVec (fun S ↦ S.refVec Ω) (initialFrames L w)) -
          framesVec (fun S ↦ S.refVec Ω) (terminalFrames L w)‖ ≤
        (sweepOperationCount L w : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ)) := by
  have hnorm : ‖toEuclideanLin (sweepMiddleCircuit c).op (framesVec (fun S ↦ S.refVec Ω)
      (initialFrames L w))‖ ≤ 1 :=
    ((sweepMiddleCircuit c).norm_toEuclideanLin_op_le _).trans (norm_initialFrames hΩ).le
  refine ⟨hnorm, ?_⟩
  let a := middleSystem (L := L) (w := w) (q := q)
  let step := sweepMiddleStep c
  let N := sweepOperationCount L w
  let ref : (n : ℕ) → EuclideanSpace ℂ (Config (a n)) := fun n ↦
    framesVec (fun S ↦ S.refVec Ω) (operationFrames L w n)
  let x : (n : ℕ) → EuclideanSpace ℂ (Config (a n)) := fun n ↦
    toEuclideanLin (OriginalCircuit.sequence a step n).op (ref 0)
  let S : (n : ℕ) → EuclideanSpace ℂ (Config (a n)) →ₗ[ℂ] EuclideanSpace ℂ (Config (a (n + 1))) :=
    fun n ↦ toEuclideanLin (step n).op
  have herr : ‖x N - ref N‖ ≤ ∑ n ∈ Finset.range N, ‖S n (ref n) - ref (n + 1)‖ :=
    TNLean.norm_trajectory_sub_reference_le S x ref N
      (fun n _ v ↦ (step n).norm_toEuclideanLin_op_le v)
      (by simp only [x, OriginalCircuit.op_sequence_zero, Matrix.toEuclideanLin_one_apply])
      (fun n _ ↦ by
        simp only [x, S, OriginalCircuit.op_sequence_succ, Matrix.toEuclideanLin_mul_apply])
  have herr' : ‖x N - ref N‖ ≤ (N : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    refine herr.trans ?_
    calc
      _ ≤ ∑ _n ∈ Finset.range N, 4 * (L : ℝ) ^ (-12 : ℤ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hb := (middleStep_bounded c Ω hc n).norm_op_sub_le
        have hn' : n < sweepOperationCount L w := Finset.mem_range.mp hn
        simpa only [S, step, ref, ite_eq_left hn'] using hb
      _ = _ := by simp
  unfold sweepMiddleCircuit
  rw [castFrames_error _ (operationFrames_zero L w)
    (operationFrames_last (L := L) (w := w)) Ω]
  exact herr'

end TNLean.MPS.AreaLaw.ChainSweep
