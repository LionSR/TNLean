/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolTerminalCoordinates
import TNLean.Lattice.Sheet.SheetStack

/-!
# Private initialization of the chain sheets

The main copy is held by the first remainder party. Every right and left
auxiliary copy is held by the party that supplies its band operation. Copies
with the same centre remain distinct occurrences in the list of sheets.
The product of the copies can therefore be prepared from a product vector
across the parties using private operations alone.

Source: the one-dimensional note, Part II, `part2b_mps_protocol.tex`,
Construction `con:sweep`, lines 330–343, and Proposition `prop:sweep`,
item 1, lines 349–351. This is the initialization of the specified copies;
it does not construct the subsequent sweep or its information estimates.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.Lattice TNLean.PEPS.PairEffect

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
    ‖framesVec (Sheet.refFamily Ω) (initialFrames L w)‖ = 1 :=
  Sheet.norm_framesVec hΩ _

/-- The specified initial copies are prepared exactly from a product vector
across all parties, with no nonprivate gate. The memory and vector of each
party are constructed from the copies it holds, rather than supplied.
Source: Part II, `prop:sweep`, item 1, lines 349–351. -/
theorem exists_initialization {L w q : ℕ}
    (hL : 0 < L) {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) :
    let Fs := initialFrames L w
    let holder : Sheet (Fin L) (Party L w) → Party L w := fun F ↦ F.owner ⟨0, hL⟩
    ∃ hx : ∀ p, ‖framesVec (Sheet.refFamily Ω) (Fs.filter fun F ↦ holder F = p)‖ = 1,
      ∃ c : OriginalCircuit
          (ProductInput.wholePartyLayout fun p ↦
            framesSpace (Sheet.regs q) (Fs.filter fun F ↦ holder F = p))
          (stackRegs (Sheet.regs q) Fs []),
        c.nonprivateCount = 0 ∧
        (∀ (S : Set (Party L w)) g, (↑(c.participants g) : Set (Party L w)) ⊆ S) ∧
        (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
        c.eval (ProductInput.ofAllParties _ _ hx).vector = framesVec (Sheet.refFamily Ω) Fs := by
  classical
  apply Sheet.exists_originalCircuit_initial_of_owner hΩ
  intro F hF x
  obtain ⟨p, rfl⟩ := mem_initialFrames hF
  rfl

end TNLean.MPS.AreaLaw.ChainSweep
