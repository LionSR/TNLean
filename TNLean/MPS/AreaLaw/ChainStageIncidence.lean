/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolTerminalCoordinates
import TNLean.MPS.AreaLaw.BandDissolution
import TNLean.Lattice.PartyCircuit.OriginalCircuitSequence
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Aesop

/-!
# Participants in the prescribed chain stages

This module counts the prescribed primitive positions. No circuit or sweep is
constructed here.

A stage has two births, eight positions for the left band, and eight positions
for the right band. At stage zero the left band is its boundary death followed
by empty positions. Each other band uses exactly `OneBand.participants`.
The positions overcount nonprivate occurrences: an exchange is private, and
empty positions do not stand for a gate.

The participant incidence is derived from the actual party labels. A remainder
party occurs only in its own stage or the preceding stage. The completed party
with zero-based index j occurs only in stages j and j + 1. Consequently the
18 positions in each of at most two stages give at most 36 occurrences.

This is a combinatorial assertion about the prescribed primitive positions.
An actual sweep must still construct its original circuits and identify their
nonprivate occurrences with these positions. Its chronological composition and
participation sums are the existing `OriginalCircuit.sequence`,
`nonprivateCount_sequence`, and `participationCount_sequence`; no second circuit
structure or assumed lifetime bound is introduced here.

Source: the one-dimensional note, Part II, `part2b_mps_protocol.tex`,
Construction `con:sweep`, lines 329–342, and Proposition `prop:sweep`, lines 349–360.
-/

noncomputable section

open scoped BigOperators

namespace TNLean.MPS.AreaLaw.ChainSweep

variable {L w : ℕ}

/-- The predecessor completed-block party is used only at a positive stage.
Source: Part II, `con:sweep`, lines 333–338. -/
private def predecessorParty (k : Fin (stageCount L w)) (hk : 0 < k.val) : Party L w :=
  .inr ⟨k.val - 1, by omega⟩

/-- Actual participants of the two births and the two prescribed band operations.
Slots 2–9 at stage zero contain the direct boundary death and empty padding.
Source: Part II, `con:sweep`, lines 333–342, and `con:band`, lines 263–275. -/
def stageParticipants (k : Fin (stageCount L w)) (j : Fin 18) : Set (Party L w) :=
  if h₀ : j.val = 0 then {Sum.inl k.castSucc, Sum.inl k.succ}
  else if h₁ : j.val = 1 then {Sum.inl k.castSucc, Sum.inr k}
  else if hleft : j.val < 10 then
    if hk : 0 < k.val then
      OneBand.participants (Sum.inl k.castSucc) (Sum.inr k) (predecessorParty k hk)
        ⟨j.val - 2, by omega⟩
    else if j.val = 2 then {Sum.inr k, Sum.inl k.castSucc} else ∅
  else
    OneBand.participants (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k)
      ⟨j.val - 10, by omega⟩

/-- Every participant in one of the eight band positions is one of its three
specified parties. Source: Part II, `con:band`, lines 263–275. -/
private theorem mem_bandParticipants_roles {P : Type} (A B C p : P) (j : Fin 8)
    (hp : p ∈ OneBand.participants A B C j) : p = A ∨ p = B ∨ p = C := by
  fin_cases j <;> simp [OneBand.participants] at hp <;> aesop

/-- All stage roles are explicit; a predecessor party is never formed at stage zero.
Source: Part II, `con:sweep`, lines 333–342. -/
private theorem stageParticipants_roles (k : Fin (stageCount L w)) (j : Fin 18)
    (p : Party L w) (hp : p ∈ stageParticipants k j) :
    p = Sum.inl k.castSucc ∨ p = Sum.inl k.succ ∨ p = Sum.inr k ∨
      ∃ hk : 0 < k.val, p = predecessorParty k hk := by
  classical
  unfold stageParticipants at hp
  split_ifs at hp with h₀ h₁ hleft hk hboundary
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    aesop
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    aesop
  · rcases mem_bandParticipants_roles _ _ _ _ _ hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨hk, h⟩))
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    aesop
  · exact hp.elim
  · rcases mem_bandParticipants_roles _ _ _ _ _ hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

/-- A remainder party at position r can be used only at stages r or r - 1.
Source: Part II, `con:sweep`, lines 333–342. -/
theorem remainder_participating_stage (r : Fin (stageCount L w + 1))
    (k : Fin (stageCount L w)) (j : Fin 18)
    (hp : Sum.inl r ∈ stageParticipants k j) : k.val = r.val ∨ k.val + 1 = r.val := by
  rcases stageParticipants_roles k j _ hp with h | h | h | ⟨hk, h⟩
  · exact Or.inl (congrArg Fin.val (Sum.inl.inj h)).symm
  · exact Or.inr (congrArg Fin.val (Sum.inl.inj h)).symm
  · cases h
  · cases h

/-- The completed party at position r is P_(r+1), and is used only at stages
r and r + 1. Source: Part II, `con:sweep`, lines 333–342. -/
theorem completed_participating_stage (r : Fin (stageCount L w))
    (k : Fin (stageCount L w)) (j : Fin 18)
    (hp : Sum.inr r ∈ stageParticipants k j) : k.val = r.val ∨ k.val = r.val + 1 := by
  rcases stageParticipants_roles k j _ hp with h | h | h | ⟨hk, h⟩
  · cases h
  · cases h
  · exact Or.inl (congrArg Fin.val (Sum.inr.inj h)).symm
  · have hr : r.val = k.val - 1 := congrArg Fin.val (Sum.inr.inj h)
    exact Or.inr (by omega)

/-- The possible adjacent stage indices derived from a party's own label.
This set is an upper bound, not a hypothesis about participation.
Source: Part II, `con:sweep`, lines 333–342. -/
def adjacentStageIndices : Party L w → Finset ℕ
  | .inl r => {r.val - 1, r.val}
  | .inr r => {r.val, r.val + 1}

/-- An actual participating position has an index in the two adjacent stages.
Source: Part II, `con:sweep`, lines 333–342. -/
theorem stageIndex_mem_adjacent (k : Fin (stageCount L w)) (j : Fin 18)
    (p : Party L w) (hp : p ∈ stageParticipants k j) :
    k.val ∈ adjacentStageIndices p := by
  cases p with
  | inl r =>
      have h := remainder_participating_stage r k j hp
      simp only [adjacentStageIndices, Finset.mem_insert, Finset.mem_singleton]
      omega
  | inr r =>
      simpa only [adjacentStageIndices, Finset.mem_insert, Finset.mem_singleton] using
        completed_participating_stage r k j hp

/-- The actual labelled stage-slot occurrences involving one party. Auxiliary
copies are never identified by their centre in this indexing.
Source: Part II, `con:sweep`, lines 333–342, and `prop:sweep`, lines 351–355. -/
def stageOccurrences (p : Party L w) : Finset (Fin (stageCount L w) × Fin 18) := by
  classical
  exact Finset.univ.filter fun e ↦ p ∈ stageParticipants e.1 e.2

/-- Stage indices that actually occur for the prescribed participant sets.
Source: Part II, `con:sweep`, lines 333–342. -/
def participatingStageIndices (p : Party L w) : Finset ℕ :=
  (stageOccurrences p).image fun e ↦ e.1.val

/-- Adjacency is obtained from the explicit participants, not assumed.
Source: Part II, `con:sweep`, lines 333–342. -/
theorem participatingStageIndices_subset (p : Party L w) :
    participatingStageIndices p ⊆ adjacentStageIndices p := by
  classical
  intro k hk
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
  exact stageIndex_mem_adjacent e.1 e.2 p (Finset.mem_filter.mp he).2

/-- A party occurs in at most two adjacent stages of the prescribed schedule.
Source: Part II, `prop:sweep`, lifetime assertion at lines 353–355. -/
theorem participatingStageIndices_card_le_two (p : Party L w) :
    (participatingStageIndices p).card ≤ 2 := by
  classical
  calc
    (participatingStageIndices p).card ≤ (adjacentStageIndices p).card :=
      Finset.card_le_card (participatingStageIndices_subset p)
    _ ≤ 2 := by cases p <;> exact Finset.card_le_two

/-- The count concerns prescribed primitive positions, not an unconstructed circuit.
Source: Part II, `prop:sweep`, lifetime assertion at lines 353–355. -/
def scheduledParticipationCount (p : Party L w) : ℕ := (stageOccurrences p).card

open Classical in
/-- Counting the actual stage-slot pairs equals summing the per-stage counts.
This is the finite-sum form used by `OriginalCircuit.participationCount_sequence`
when the actual stages are assembled; it is not yet a circuit-count identity.
Source: Part II, `con:sweep`, lines 333–342. -/
theorem scheduledParticipationCount_eq_sum (p : Party L w) :
    scheduledParticipationCount p =
      ∑ k : Fin (stageCount L w),
        ((Finset.univ : Finset (Fin 18)).filter fun j ↦
          p ∈ stageParticipants k j).card := by
  classical
  unfold scheduledParticipationCount stageOccurrences
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]

/-- The 18 labelled positions in each of at most two stages give a lifetime
upper bound of 36. This is a combinatorial bound only.
Source: Part II, `con:sweep`, lines 333–342, and `prop:sweep`, lines 353–355. -/
theorem scheduledParticipationCount_le_thirtySix (p : Party L w) :
    scheduledParticipationCount p ≤ 36 := by
  classical
  let f : Fin (stageCount L w) × Fin 18 → ℕ × Fin 18 := fun e ↦ (e.1.val, e.2)
  have hf : Function.Injective f := by
    intro e e' h
    change (e.1.val, e.2) = (e'.1.val, e'.2) at h
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst h)
    · exact congrArg (fun z : ℕ × Fin 18 ↦ z.2) h
  have hsub : (stageOccurrences p).image f ⊆
      participatingStageIndices p ×ˢ (Finset.univ : Finset (Fin 18)) := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨d, hd, rfl⟩,
      Finset.mem_univ _⟩
  calc
    scheduledParticipationCount p = ((stageOccurrences p).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ ≤ (participatingStageIndices p ×ˢ (Finset.univ : Finset (Fin 18))).card :=
      Finset.card_le_card hsub
    _ = (participatingStageIndices p).card * 18 := by simp
    _ ≤ 2 * 18 := Nat.mul_le_mul_right 18 (participatingStageIndices_card_le_two p)
    _ = 36 := by norm_num

/-- The source's participation constant 40 follows for the prescribed positions.
Its transfer to an actual circuit still requires the occurrence identification.
Source: Part II, `prop:sweep`, lines 353–355. -/
theorem scheduledParticipationCount_le_forty (p : Party L w) :
    scheduledParticipationCount p ≤ 40 :=
  (scheduledParticipationCount_le_thirtySix p).trans (by omega)

end TNLean.MPS.AreaLaw.ChainSweep
