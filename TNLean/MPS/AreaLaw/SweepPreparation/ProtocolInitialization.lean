/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolTerminalCoordinates
import QICLean.Circuit.Party.Sheet.Initialization

/-!
# Private initialization of the chain sheets

The main copy is held by the first remainder party. Every right and left
auxiliary copy is held by the party that supplies its band operation. Copies
with the same centre remain distinct occurrences in the list of sheets.
The reference vector of the copies is therefore a product of unit vectors
across the parties, the factor of a party being the product of the copies it holds.

Source: the one-dimensional note, Part II, `part2b_mps_protocol.tex`,
Construction `con:sweep`, lines 330–343, and Proposition `prop:sweep`,
item 1, lines 349–351. This is the initialization of the specified copies;
it does not construct the subsequent sweep or its information estimates.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open QuantumCircuit QuantumCircuit.Party
open ManyBody (Config)

/-- All auxiliary copy labels, each occurring once, in a fixed order.
Source: Part II, `con:band`, lines 265–272, and `con:sweep`, lines 336–340. -/
def initialAuxiliaryOrder (L w : ℕ) : List (AuxiliaryCopy L w) :=
  Finset.univ.toList

/-- The initial holder is C of the corresponding band operation. A right copy
at stage k is held by P_(k+1); a left copy at stage k+1 is held by P_(k+1).
Source: Part II, `prop:sweep`, item 1, lines 349–351. -/
def initialAuxiliaryHolder (L w : ℕ) : AuxiliaryCopy L w → Party L w
  | .inl k => .inr k
  | .inr k => .inr ⟨k.val, by omega⟩

/-- The main copy at R_0, followed by the distinct labelled auxiliary copies,
initially held privately at their actual band holders.
Source: Part II, `prop:sweep`, item 1, lines 349–351. -/
def initialFrames (L w : ℕ) :
    List (Sheet (Fin L) (Party L w)) :=
  Sheet.mk (fun _ ↦ .inl (0 : Fin (stageCount L w + 1))) ::
    (initialAuxiliaryOrder L w).map fun c ↦
      Sheet.mk (fun _ ↦ initialAuxiliaryHolder L w c)

/-- There is one main copy, m right copies and m−1 left copies, with truncated
subtraction when m=0. Source: Part II, `con:sweep`, lines 330–343. -/
theorem length_initialFrames (L w : ℕ) :
    (initialFrames L w).length =
      1 + stageCount L w + (stageCount L w - 1) := by
  simp [initialFrames, initialAuxiliaryOrder, AuxiliaryCopy, Fintype.card_sum]
  omega

/-- Every initial sheet is held entirely by one party.
Source: Part II, `prop:sweep`, item 1, lines 349–351. -/
theorem mem_initialFrames {L w : ℕ}
    {F : Sheet (Fin L) (Party L w)} (hF : F ∈ initialFrames L w) :
    ∃ p : Party L w, F = Sheet.mk (fun _ ↦ p) := by
  rcases List.mem_cons.1 (by simpa only [initialFrames] using hF) with rfl | hF
  · exact ⟨_, rfl⟩
  · obtain ⟨c, _, rfl⟩ := List.mem_map.1 hF
    exact ⟨_, rfl⟩

/-- The actual product of all initial copies has norm one.
Source: Part II, `prop:sweep`, item 1, lines 349–351. -/
theorem norm_initialFrames {L w q : ℕ}
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) :
    ‖framesVec (fun S : Sheet (Fin L) (Party L w) ↦ S.refVec Ω) (initialFrames L w)‖ = 1 := by
  rw [norm_framesVec]
  exact List.prod_eq_one fun r hr ↦ by
    obtain ⟨S, -, rfl⟩ := List.mem_map.mp hr
    rw [S.norm_refVec, hΩ]

/-- The specified initial copies form a product of unit vectors across all parties: the factor
of a party is the product of the copies it holds, constructed rather than supplied.
Source: Part II, `prop:sweep`, item 1, lines 349–351. -/
theorem exists_initialization {L w q : ℕ}
    (hL : 0 < L) {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) :
    ∃ φ : ∀ p, EuclideanSpace ℂ
        (stackSystem (Sheet.system q) (initialFrames L w) (fun _ ↦ Unit) p),
      (∀ p, ‖φ p‖ = 1) ∧
      (WithLp.toLp 2 (productVector fun p x ↦ WithLp.ofLp (φ p) x) :
        EuclideanSpace ℂ (Config (stackSystem (Sheet.system q) (initialFrames L w)
          fun _ ↦ Unit))) =
        framesVec (fun S ↦ S.refVec Ω) (initialFrames L w) :=
  Sheet.exists_productVector_eq_framesVec hΩ _ (fun F ↦ F.owner ⟨0, hL⟩) fun F hF x ↦ by
    obtain ⟨p, rfl⟩ := mem_initialFrames hF
    rfl

end TNLean.MPS.AreaLaw.ChainSweep
