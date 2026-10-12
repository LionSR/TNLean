/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.TouchedLabels

/-! # Labels at nonempty original gate occurrences

The all-party expansion requests exactly these labels. Empty-participant
operations retain their aggregate scalar and require no choice.
Source: polynomial-PEPS, `04-compression.tex`, lines 351–381 and 565–573.
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

/-- The occurrences expanded by the all-party partial expansion are precisely
those having an original participating party.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem isTouched_all_iff {a b : Layout P} (w : SourceCircuit a b) (g : w.gateLocations) :
    w.IsTouched (fun _ => true) g ↔ (w.participants g).Nonempty := by
  constructor
  · rintro ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, hp, rfl⟩

/-- The original chronological occurrences whose participant sets are nonempty.
These are the shared gate stars; empty-participant operations are retained in
the aggregate scalar factor. Source: polynomial-PEPS 04-compression.tex,
lines 351–381 and 565–573. -/
def nonemptyGateLocations {a b : Layout P} (w : SourceCircuit a b) : Type :=
  {g : w.gateLocations // (w.participants g).Nonempty}

/-- There are finitely many nonempty-participant original occurrences.
Source: polynomial-PEPS 04-compression.tex, lines 565–573. -/
instance nonemptyGateLocationsFintype {a b : Layout P} (w : SourceCircuit a b) :
    Fintype w.nonemptyGateLocations := by
  classical
  unfold nonemptyGateLocations
  infer_instance

/-- The actual all-party choices are exactly the labels on the nonempty
original participant occurrences. No label is requested at an empty occurrence.
Source: polynomial-PEPS 04-compression.tex, lines 351–381 and 565–573. -/
def allChoicesNonemptyLabelsEquiv {a b : Layout P} (w : SourceCircuit a b) :
    Choices (fun _ => true) w ≃ ((g : w.nonemptyGateLocations) → w.branchLabels g.1) :=
  (choicesTouchedLabelsEquiv (fun _ => true) w).trans {
    toFun := fun ξ g => ξ g.1 ((isTouched_all_iff w g.1).mpr g.2)
    invFun := fun ξ g hg => ξ ⟨g, (isTouched_all_iff w g).mp hg⟩
    left_inv := fun ξ => by funext g hg; rfl
    right_inv := fun ξ => by funext g; cases g; rfl }

/-- The equivalence preserves the exact label of the original occurrence.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem allChoicesNonemptyLabelsEquiv_apply {a b : Layout P} (w : SourceCircuit a b)
    (ξ : Choices (fun _ => true) w) (g : w.nonemptyGateLocations) :
    allChoicesNonemptyLabelsEquiv w ξ g =
      choiceAt (fun _ => true) w ξ g.1 ((isTouched_all_iff w g.1).mpr g.2) := rfl

end TNLean.PEPS.PairEffect.SourceCircuit
