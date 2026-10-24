/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ChainStageIncidence
import Mathlib.Data.Finset.Card

/-!
# Three-party bound for the prescribed chain positions

Every finite subset of the actual participants of one prescribed stage
position has at most three elements.
The bound follows from the existing participant table, including the direct
left death and empty positions at stage zero. No distinctness, positive
width, separation or physical hypothesis is required.

This is a finite-set auxiliary result. It neither constructs local circuits
nor supplies their support; an actual circuit's existing stage-support
conclusion is the input needed to apply it to that circuit's participants.

Source: the one-dimensional note, Part II, `con:band`, lines 263–275,
`con:sweep`, lines 330–342, and the three-party assertion in `prop:sweep`,
lines 353–355 of `part2b_mps_protocol.tex`.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

/-- Each prescribed band position uses a subset of its three designated
roles. Coincident roles only decrease the cardinality.
Source: Part II, `con:band`, lines 263–275. -/
private theorem card_le_three_of_subset_bandParticipants {P : Type}
    (s : Finset P) (A B C : P) (j : Fin 8)
    (hsub : (↑s : Set P) ⊆ OneBand.participants A B C j) : s.card ≤ 3 := by
  classical
  have hroles : s ⊆ ({A, B, C} : Finset P) := by
    intro p hp
    have hm := hsub hp
    fin_cases j <;>
      simp only [OneBand.participants, Set.mem_insert_iff, Set.mem_singleton_iff,
        Finset.mem_insert, Finset.mem_singleton] at hm ⊢ <;> aesop
  exact (Finset.card_le_card hroles).trans Finset.card_le_three

/-- A finite set contained in the actual participants of one prescribed chain
position has at most three parties, including the first stage's boundary
operation and empty padding. No stage geometry or distinct-role premise is
needed for this cardinal bound.
Source: Part II, `con:band`, `con:sweep`, and the three-party assertion in
`prop:sweep`, lines 263–275, 330–342 and 353–355. -/
theorem card_le_three_of_subset_stageParticipants {L w : ℕ}
    (s : Finset (Party L w)) (k : Fin (stageCount L w)) (j : Fin 18)
    (hsub : (↑s : Set (Party L w)) ⊆ stageParticipants k j) : s.card ≤ 3 := by
  classical
  have hpair (A B : Party L w)
      (h : (↑s : Set (Party L w)) ⊆ ({A, B} : Set (Party L w))) : s.card ≤ 3 := by
    have hfin : s ⊆ ({A, B} : Finset (Party L w)) := by
      intro p hp
      simpa only [Finset.mem_insert, Finset.mem_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] using h hp
    calc
      s.card ≤ ({A, B} : Finset (Party L w)).card := Finset.card_le_card hfin
      _ ≤ 2 := Finset.card_le_two
      _ ≤ 3 := by decide
  unfold stageParticipants at hsub
  split_ifs at hsub with h₀ h₁ hleft hk hboundary
  · exact hpair _ _ hsub
  · exact hpair _ _ hsub
  · exact card_le_three_of_subset_bandParticipants s _ _ _ _ hsub
  · exact hpair _ _ hsub
  · have he : s ⊆ (∅ : Finset (Party L w)) := fun _ hp ↦ (hsub hp).elim
    exact (Finset.card_le_card he).trans (by simp)
  · exact card_le_three_of_subset_bandParticipants s _ _ _ _ hsub

end TNLean.MPS.AreaLaw.ChainSweep
