/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NonemptyGateLabels
import TNLean.PEPS.Approximation.DistributedOperatorContraction
import TNLean.PEPS.Approximation.PartySelector

/-! # Gate labels visible at one party

For the all-party grouping, the occurrences touched by the grouped owner of an
original party are exactly the gates in which it participates. The partial
choice at that party is therefore reconstructed from the labels carried by its
incident gate stars, and this reconstruction agrees with projecting a global
choice.

Source: polynomial-PEPS, `04-compression.tex`, lines 351–381 and 565–579.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}
open TNLean.PEPS.Approximation

/-- The all-party grouping retains every original party with its actual label.
Source: polynomial-PEPS 04-compression.tex, lines 409–417. -/
theorem partySelector_affectedOwner_all_apply (p q : P) :
    partySelector (some (⟨p, rfl⟩ : {p : P // (fun _ : P => true) p = true}))
        (affectedOwner (fun _ => true) q) = partySelector p q := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp [partySelector, affectedOwner]

/-- Selecting the grouped owner of one original party touches exactly its
original incident gates. Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem isTouched_groupedParty_iff {a b : Layout P} (w : SourceCircuit a b)
    (p : P) (g : w.gateLocations) :
    w.IsTouched (fun q => partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P => true) q)) g ↔ p ∈ w.participants g := by
  constructor
  · rintro ⟨q, hq, hsel⟩
    have hs : partySelector p q = true :=
      (partySelector_affectedOwner_all_apply p q).symm.trans hsel
    have hqp : q = p := by simpa only [partySelector, decide_eq_true_eq] using hs
    subst q
    exact hq
  · intro hp
    refine ⟨p, hp, ?_⟩
    exact (partySelector_affectedOwner_all_apply p p).trans
      (by simp only [partySelector, decide_true])

open Classical in
/-- The actual shared original-gate labels visible at one party.
Source: polynomial-PEPS 04-compression.tex, lines 565–579. -/
abbrev OriginalGateLabelsAt {a b : Layout P} (w : SourceCircuit a b) (p : P) :=
  DistributedOperatorContraction.GateLabelsAt
    (Finset.univ : Finset w.nonemptyGateLocations)
    (fun g => w.participants g.1) (fun g => w.branchLabels g.1) p

open Classical in
/-- Construct the actual incident partial choices from the gate labels carried
by the party's shared stars. Source: polynomial-PEPS 04-compression.tex,
lines 351–381 and 565–579. -/
def choicesOfOriginalGateLabelsAt {a b : Layout P} (w : SourceCircuit a b) (p : P)
    (ξ : OriginalGateLabelsAt w p) :
    Choices (fun q => partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P => true) q)) w :=
  choicesOfTouchedLabels _ w (fun g hg =>
    let hp := (isTouched_groupedParty_iff w p g).mp hg
    ξ ⟨⟨⟨g, ⟨p, hp⟩⟩, Finset.mem_univ _⟩, hp⟩)

open Classical in
/-- Restrict the labels of a genuine all-party choice to the stars visible at
an original party. Source: polynomial-PEPS 04-compression.tex, lines 565–579. -/
def originalGateLabelsAtOfAllChoices {a b : Layout P} (w : SourceCircuit a b) (p : P)
    (ξ : Choices (fun _ => true) w) : OriginalGateLabelsAt w p :=
  fun g => allChoicesNonemptyLabelsEquiv w ξ g.1.1

open Classical in
/-- The incident choices reconstructed from shared stars are precisely the
restriction of the actual all-party choices. No unused gate label is chosen.
Source: polynomial-PEPS 04-compression.tex, lines 351–381 and 565–579. -/
theorem choicesOfOriginalGateLabelsAt_eq_projectAllChoices {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ξ : Choices (fun _ => true) w) :
    choicesOfOriginalGateLabelsAt w p (originalGateLabelsAtOfAllChoices w p ξ) =
      projectAllChoices (fun q => partySelector (some ⟨p, rfl⟩)
        (affectedOwner (fun _ : P => true) q)) w ξ := by
  apply (choicesTouchedLabelsEquiv _ w).injective
  funext g hg
  exact (choiceAt_choicesOfTouchedLabels _ w _ g hg).trans
    (choiceAt_projectAllChoices _ w ξ g hg).symm

end TNLean.PEPS.PairEffect.SourceCircuit
