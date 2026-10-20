/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitChoiceAt
import TNLean.Lattice.PartyCircuit.DistributedSourceComposition

/-! # Partial choices as labels at touched occurrences

A partial choice for a selected set of parties is the same datum as one branch
label at each gate occurrence touched by that set. The equivalence holds for
empty branch types as well. Keeping the labels of an all-party choice at the
occurrences touched by the selected parties projects it to their partial choice.

Source: polynomial-PEPS, `04-compression.tex`, lines 351–381.
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

/-- Labels at exactly the chronological occurrences touched by the selected
parties. An untouched occurrence contributes no label.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
def TouchedLabels (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b) : Type :=
  (g : w.gateLocations) → w.IsTouched A g → w.branchLabels g

/-- Construct the actual partial choices from the labels at touched occurrences.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
def choicesOfTouchedLabels (A : P → Bool) : {a b : Layout P} → (w : SourceCircuit a b) →
    TouchedLabels A w → Choices A w
  | _, _, .id _, _ => ()
  | _, _, .comp w v, ξ =>
      (choicesOfTouchedLabels A w (fun g hg => ξ (.inl g) hg),
        choicesOfTouchedLabels A v (fun g hg => ξ (.inr g) hg))
  | _, _, .localMap .., _ => ()
  | _, _, @SourceCircuit.gate _ C ι _ _ owner a b c G tail, ξ => by
      classical
      by_cases h : ∃ q : C, A (owner q) = true
      · exact (Equiv.cast (by simp only [Choices, ite_eq_left h]) :
          Choices A (.gate owner G tail) ≃ ι).symm
          (ξ () ((isTouched_gate_iff A owner G tail).mpr h))
      · exact (Equiv.cast (by simp only [Choices, ite_eq_right h])).symm ()
  | _, _, .swap .., _ => ()
  | _, _, .frame _ w, ξ => choicesOfTouchedLabels A w ξ

/-- Recovering the label of a touched occurrence returns the prescribed label.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem choiceAt_choicesOfTouchedLabels (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : TouchedLabels A w) (g : w.gateLocations)
    (hg : w.IsTouched A g) :
    choiceAt A w (choicesOfTouchedLabels A w ξ) g hg = ξ g hg := by
  induction w with
  | id => exact nomatch g
  | comp w v ihw ihv =>
      cases g with
      | inl g => exact ihw (fun g hg => ξ (.inl g) hg) g hg
      | inr g => exact ihv (fun g hg => ξ (.inr g) hg) g hg
  | localMap => exact nomatch g
  | @gate C ι _ _ owner a b c G tail =>
      cases g
      have ht := (isTouched_gate_iff A owner G tail).mp hg
      simp only [choicesOfTouchedLabels, dite_eq_left ht]
      dsimp only [choiceAt]
      exact Equiv.apply_symm_apply _ _
  | swap => exact nomatch g
  | frame r w ih => exact ih ξ g hg

/-- The recovered chronological labels reconstruct the actual partial choices.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem choicesOfTouchedLabels_choiceAt (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w) :
    choicesOfTouchedLabels A w (choiceAt A w ξ) = ξ := by
  induction w with
  | id =>
      change () = ξ
      exact Subsingleton.elim _ _
  | comp w v ihw ihv => exact congrArg₂ Prod.mk (ihw ξ.1) (ihv ξ.2)
  | localMap =>
      change () = ξ
      exact Subsingleton.elim _ _
  | @gate C ι _ _ owner a b c G tail =>
      classical
      by_cases ht : ∃ q : C, A (owner q) = true
      · simp only [choicesOfTouchedLabels, dite_eq_left ht]
        dsimp only [choiceAt]
        exact Equiv.symm_apply_apply _ _
      · have : Subsingleton (Choices A (.gate owner G tail)) := by
          simp only [Choices, ite_eq_right ht]
          infer_instance
        exact Subsingleton.elim _ _
  | swap =>
      change () = ξ
      exact Subsingleton.elim _ _
  | frame r w ih => exact ih ξ

/-- Actual partial choices are equivalent to the labels at precisely their
incident chronological occurrences. This equivalence includes empty branch
types without an inhabitedness assumption.
Source: polynomial-PEPS 04-compression.tex, lines 351–381 and 565–573. -/
def choicesTouchedLabelsEquiv (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b) :
    Choices A w ≃ TouchedLabels A w where
  toFun ξ := choiceAt A w ξ
  invFun := choicesOfTouchedLabels A w
  left_inv := choicesOfTouchedLabels_choiceAt A w
  right_inv ξ := by
    funext g hg
    exact choiceAt_choicesOfTouchedLabels A w ξ g hg


/-- Restrict actual all-party choices to the occurrences touched by a selected
set of parties. Empty-participant gates request no label in either expansion.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
def projectAllChoices (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (ξ : Choices (fun _ => true) w) : Choices A w :=
  choicesOfTouchedLabels A w fun g hg =>
    choiceAt (fun _ => true) w ξ g (by obtain ⟨p, hp, _⟩ := hg; exact ⟨p, hp, rfl⟩)

/-- A retained partial choice is the original label of the same occurrence in
the actual all-party expansion. Source: polynomial-PEPS 04-compression.tex,
lines 351–381. -/
theorem choiceAt_projectAllChoices (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices (fun _ => true) w) (g : w.gateLocations)
    (hg : w.IsTouched A g) :
    choiceAt A w (projectAllChoices A w ξ) g hg =
      choiceAt (fun _ => true) w ξ g
        (by obtain ⟨p, hp, _⟩ := hg; exact ⟨p, hp, rfl⟩) :=
  choiceAt_choicesOfTouchedLabels A w _ g hg

end TNLean.PEPS.PairEffect.SourceCircuit
