/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolParties
import TNLean.PEPS.Approximation.HomogeneousOwnership
import TNLean.PEPS.Approximation.SheetStackEndpoints

/-!
# Owners of the guides of a repainting, and empty changes

The guides of the dyadic repainting schedule carry labels in `GuideLabel`, and during the
repainting of a square a label is read as a party by `labelParty`, which is injective on the
labels of the genuine squares and the placeholder (`labelParty_injOn`). This file shows that every
guide used inside the repainting of a genuine block, the main guide after the central birth and
any completed edges and every main or auxiliary guide of an edge construction, takes only such
labels (`blockRepainting_mem_validLabels`). With `labelParty_injOn`, two sites of these guides
have the same owner party exactly when they carry the same label: the owners of the encoded
frames of the guides are read faithfully from their labels (`06-geometry.tex`, lines 82–100 and
585–609).

It also records the identity change for a birth or death whose raw target is empty: the frame
is unchanged (`EncodedFrame.Frame.changeOwner_empty`), and the change is the original circuit
without operations (`emptyTarget_step`). Such targets arise when nominal labels coincide and at
blocks outside the genuine lattice (`06-geometry.tex`, lines 432–438).

## Main results

* `TNLean.PEPS.Approximation.blockRepainting_mem_validLabels`.
* `TNLean.PEPS.Approximation.newParty_mem_validLabels`.
* `TNLean.PEPS.EncodedFrame.Frame.changeOwner_empty`, `TNLean.PEPS.Approximation.emptyTarget_step`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`: the level schedule and the placeholder (lines 82–100), coalescing labels and
  empty targets (lines 432–438), and the active labels (lines 585–609).
-/

noncomputable section

namespace TNLean.PEPS.EncodedFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type*}

/-- Changing the owner of an empty set of raw registers leaves the frame unchanged. -/
@[simp] theorem Frame.changeOwner_empty (F : Frame pos q Party) (Q : Party) :
    F.changeOwner ∅ Q = F := by
  cases F
  simp [Frame.changeOwner]

end TNLean.PEPS.EncodedFrame

namespace TNLean.PEPS.Approximation

open Set EncodedFrame PairEffect

/-! ### Empty targets -/

/-- **A birth or death with empty target.** When the raw target is empty, the birth leaves the
frame unchanged, and it is the change without operations: no nonprivate gate and no reference
error. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 432–438 (“Empty physical targets
need no information estimate”). -/
theorem emptyTarget_step {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q]
    {pos : ι → ℝ × ℝ} {Party : Type} (Ω : EuclideanSpace ℂ (ι → Fin q))
    (F : Frame pos q Party) (Q : Party) :
    ∃ c : OriginalCircuit F.regs (F.changeOwner ∅ Q).regs, c.nonprivateCount = 0 ∧
      (∀ (S : Set Party) g, (↑(c.participants g) : Set Party) ⊆ S) ∧
      (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
      c.eval (F.regRef Ω) = (F.changeOwner ∅ Q).regRef Ω :=
  exists_originalCircuit_of_frame_eq Ω (F.changeOwner_empty Q).symm

/-! ### Labels of the guides of a repainting -/

/-- The block labels of the pass to level `2 ^ j'`, with block parties labelled by their squares
in `GuideLabel`. -/
abbrev protocolLevelLabels (k j' : ℕ) (done : Set (ℤ × ℤ)) : ℤ × ℤ → GuideLabel :=
  levelLabels ((2 : ℤ) ^ (k - j')) (oldParty Sum.inl j') (newParty Sum.inl j') guidePlaceholder
    done

/-- The new label of a genuine block of level `2 ^ j'` is the label of a square of the
hierarchy. -/
theorem newParty_mem_validLabels {k j' : ℕ} (hj : j' < k) {S : ℤ × ℤ}
    (hS : InRoot ((2 : ℤ) ^ (k - j')) S) : newParty Sum.inl j' S ∈ validLabels k := by
  classical
  have h := levelLabels_mem_validLabels hj {S} S
  simpa [levelLabels, hS] using h

/-- **Valid labels inside a repainting.** In the repainting of a genuine block `S` of level
`2 ^ j'` to its new label, every value of the main guide after the central birth and any completed
edges, and of every main or auxiliary guide of an edge construction with any of its normal words,
is the placeholder or the label of a square of the hierarchy.

Polynomial-PEPS manuscript (September 24, 2026), `06-geometry.tex`, lines 82–100 and 585–609
(equation `eq:geometry-active-labels`). -/
theorem blockRepainting_mem_validLabels {k j' : ℕ} (hj : j' < k) {n : ℝ} (hn : 0 < n)
    (done : Set (ℤ × ℤ)) {S : ℤ × ℤ} (hS : InRoot ((2 : ℤ) ^ (k - j')) S)
    (E : List SquareEdge) (e : SquareEdge) {W : ℝ → GuideLabel}
    (hW : W ∈ edgeWords (protocolLevelLabels k j' done S) (newParty Sum.inl j' S)
      (protocolLevelLabels k j' done (e.nbrBlock S))) (p : ℝ × ℝ) :
    (blockBaseline hn (protocolLevelLabels k j' done) S (newParty Sum.inl j' S)).completedGuide
        E p ∈ validLabels k ∧
      (blockBaseline hn (protocolLevelLabels k j' done) S
        (newParty Sum.inl j' S)).mainGuide E e W p ∈ validLabels k ∧
      (blockBaseline hn (protocolLevelLabels k j' done) S
        (newParty Sum.inl j' S)).auxGuide e W p ∈ validLabels k := by
  set R := blockBaseline hn (protocolLevelLabels k j' done) S (newParty Sum.inl j' S)
  have key : insert R.finalLabel (range R.guide) ⊆ validLabels k := by
    rintro l (rfl | ⟨x, rfl⟩)
    · exact newParty_mem_validLabels hj hS
    · exact levelLabels_mem_validLabels hj done _
  exact ⟨key (R.completedGuide_mem E p), key ((R.mainGuide_mem E e hW p).1),
    key ((R.mainGuide_mem E e hW p).2)⟩

end TNLean.PEPS.Approximation
