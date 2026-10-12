/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitChoiceAt
import TNLean.PEPS.Approximation.DistributedSourceComposition

/-! # Projecting all-party choices to selected parties

A choice of monomial labels for the all-party expansion of a chronological
source circuit restricts to a choice for any selected set of parties: keep the
label at each occurrence touched by the selection and drop the others. The
retained labels are the original ones.

Source: polynomial-PEPS, `04-compression.tex`, lines 246–251 and 351–381.
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

/-- Restrict actual all-party choices to the occurrences touched by a selected
set of parties. Empty-participant gates request no label in either expansion.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
def projectAllChoices (A : P → Bool) : {a b : Layout P} → (w : SourceCircuit a b) →
    Choices (fun _ => true) w → Choices A w
  | _, _, .id _, _ => ()
  | _, _, .comp w v, ξ => (projectAllChoices A w ξ.1, projectAllChoices A v ξ.2)
  | _, _, .localMap .., _ => ()
  | _, _, @SourceCircuit.gate _ C ι _ _ owner a b c G tail, ξ => by
      classical
      by_cases h : ∃ q : C, A (owner q) = true
      · have ht : ∃ q : C, (fun _ : P => true) (owner q) = true := by
          obtain ⟨q, _⟩ := h
          exact ⟨q, rfl⟩
        exact (Equiv.cast (by simp only [Choices, ite_eq_left h]) :
          Choices A (.gate owner G tail) ≃ ι).symm
          (choiceAt (fun _ => true) (.gate owner G tail) ξ ()
            ((isTouched_gate_iff _ owner G tail).mpr ht))
      · exact (Equiv.cast (by simp only [Choices, ite_eq_right h])).symm ()
  | _, _, .swap .., _ => ()
  | _, _, .frame _ w, ξ => projectAllChoices A w ξ

/-- A retained partial choice is the original label of the same occurrence in
the actual all-party expansion. Source: polynomial-PEPS 04-compression.tex,
lines 351–381. -/
theorem choiceAt_projectAllChoices (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices (fun _ => true) w) (g : w.gateLocations)
    (hg : w.IsTouched A g) :
    choiceAt A w (projectAllChoices A w ξ) g hg =
      choiceAt (fun _ => true) w ξ g
        (by obtain ⟨p, hp, _⟩ := hg; exact ⟨p, hp, rfl⟩) := by
  induction w with
  | id => exact nomatch g
  | comp w v ihw ihv =>
      cases g with
      | inl g => exact ihw ξ.1 g hg
      | inr g => exact ihv ξ.2 g hg
  | localMap => exact nomatch g
  | @gate C ι _ _ owner a b c G tail =>
      cases g
      have h := (isTouched_gate_iff A owner G tail).mp hg
      have ht : ∃ q : C, (fun _ : P => true) (owner q) = true := by
        obtain ⟨q, _⟩ := h
        exact ⟨q, rfl⟩
      simp only [projectAllChoices, dite_eq_left h]
      dsimp only [choiceAt]
      exact Equiv.apply_symm_apply _ _
  | swap => exact nomatch g
  | frame r w ih => exact ih ξ g hg

end TNLean.PEPS.PairEffect.SourceCircuit
