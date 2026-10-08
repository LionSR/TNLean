/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceOnlyReduction
import TNLean.PEPS.Approximation.SourceCircuitChoiceAt

/-! # Full chronological labels and incident choices

The statements concern the explicitly constructed words, their register order,
and their restrictions to selected parties. They are auxiliary identities for
the chronological construction, before the final physical partial trace.

Source: polynomial-PEPS, `04-compression.tex`, lines 233–267 and 342–381.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-network-chronologicallocality-01
TNLean.PEPS.PairEffect.SourceCircuit.FullLabels
Provenance-ID: 8769-chronological-network-chronologicallocality-02
TNLean.PEPS.PairEffect.SourceCircuit.choiceAt_choicesOfFullLabels
Provenance-ID: 8769-chronological-network-chronologicallocality-03
TNLean.PEPS.PairEffect.SourceCircuit.choicesOfFullLabels
Provenance-ID: 8769-chronological-network-chronologicallocality-04
TNLean.PEPS.PairEffect.SourceCircuit.choicesOfFullLabels_eq_of_agree
Provenance-ID: 8769-chronological-network-chronologicallocality-05
TNLean.PEPS.PairEffect.SourceCircuit.choicesOfFullLabels_party_eq_of_agree
Provenance-ID: 8769-chronological-network-chronologicallocality-06
TNLean.PEPS.PairEffect.SourceCircuit.partySelector
-/


noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- A label for every actual chronological gate occurrence.
Source: polynomial-PEPS 04-compression.tex, lines 233–267 and 342–355. -/
def FullLabels {a b : Layout P} (w : SourceCircuit a b) : Type :=
  (g : w.gateLocations) → w.branchLabels g

/-- Restrict full chronological labels to precisely the gates touched by the
selected parties. Untouched gates retain their whole operators.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
def choicesOfFullLabels (A : P → Bool) : {a b : Layout P} → (w : SourceCircuit a b) →
    FullLabels w → Choices A w
  | _, _, .id _, _ => ()
  | _, _, .comp w v, ξ =>
      (choicesOfFullLabels A w (fun g => ξ (.inl g)),
        choicesOfFullLabels A v (fun g => ξ (.inr g)))
  | _, _, .localMap .., _ => ()
  | _, _, @SourceCircuit.gate _ C ι _ _ owner a b c G tail, ξ => by
      classical
      by_cases h : ∃ q : C, A (owner q) = true
      · exact (Equiv.cast (by simp only [Choices, branchLabels, ite_eq_left h])).symm (ξ ())
      · exact (Equiv.cast (by simp only [Choices, ite_eq_right h])).symm ()
  | _, _, .swap .., _ => ()
  | _, _, .frame _ w, ξ => choicesOfFullLabels A w ξ

/-- Restriction depends only on labels at touched chronological occurrences.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem choicesOfFullLabels_eq_of_agree (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ ζ : FullLabels w)
    (h : ∀ g, w.IsTouched A g → ξ g = ζ g) :
    choicesOfFullLabels A w ξ = choicesOfFullLabels A w ζ := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      exact congrArg₂ Prod.mk
        (ihw (fun g => ξ (.inl g)) (fun g => ζ (.inl g)) (fun g hg => h (.inl g) hg))
        (ihv (fun g => ξ (.inr g)) (fun g => ζ (.inr g)) (fun g hg => h (.inr g) hg))
  | localMap => rfl
  | @gate C ι _ _ owner a b c G tail =>
      dsimp only [choicesOfFullLabels]
      split
      · rename_i ht
        congr 1
        exact h () ((isTouched_gate_iff A owner G tail).mpr ht)
      · rfl
  | swap => rfl
  | frame r w ih => exact ih ξ ζ h

/-- Every retained choice is exactly its original full chronological label.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem choiceAt_choicesOfFullLabels (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : FullLabels w) (g : w.gateLocations)
    (hg : w.IsTouched A g) :
    choiceAt A w (choicesOfFullLabels A w ξ) g hg = ξ g := by
  induction w with
  | id => exact nomatch g
  | comp w v ihw ihv =>
      cases g with
      | inl g => exact ihw (fun g => ξ (.inl g)) g hg
      | inr g => exact ihv (fun g => ξ (.inr g)) g hg
  | localMap => exact nomatch g
  | @gate C ι _ _ owner a b c G tail =>
      cases g
      have ht := (isTouched_gate_iff A owner G tail).mp hg
      simp only [choiceAt, choicesOfFullLabels, dite_eq_left ht, Equiv.apply_symm_apply]
  | swap => exact nomatch g
  | frame r w ih => exact ih ξ g hg

/-- Select one original party while retaining its exact label.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
def partySelector (p : P) : P → Bool := by
  classical
  exact fun q => decide (q = p)

/-- The actual partial choices at one party depend only on its incident gates.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem choicesOfFullLabels_party_eq_of_agree {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ξ ζ : FullLabels w)
    (h : ∀ g, p ∈ w.participants g → ξ g = ζ g) :
    choicesOfFullLabels (partySelector p) w ξ =
      choicesOfFullLabels (partySelector p) w ζ := by
  apply choicesOfFullLabels_eq_of_agree
  rintro g ⟨q, hq, heq⟩
  have hqp : q = p := by simpa only [partySelector, decide_eq_true_eq] using heq
  subst q
  exact h g hq

end TNLean.PEPS.PairEffect.SourceCircuit
