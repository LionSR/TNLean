/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Network.IncidentFactor.IncidentSourceWordComparison

/-!
# Dependence of a branch on the given incident choices

For two choices of the expansion along all parties, the operation at an original party `p` of
the local part of the branch, read in the common slots of the expansion, is the same whenever the
two choices agree after projection to the gates touched by `p`. Gates whose cell does not contain
`p` act there as the identification of equal bases, whatever their label, including gates with an
empty cell; gates whose cell contains `p` carry the same label in both choices. No extension of the
projected choice to the other gates is selected.

## Main results

* `QuantumCircuit.Party.SourceCircuit.partyOp_partialResidual_all_eq_of_projectAllChoices_eq`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 246–267, 351–381, 409–434 and 565–588.
-/

noncomputable section

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ s, Fintype (X s)]
  [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- **Local dependence on given incident choices.** Let `ξ` and `ζ` be choices of the expansion
along all parties of a circuit `w`, and let `p` be a party. If the projections of `ξ` and `ζ` to
the expansion for the single party `p` agree, then the local parts of the two branches, read in
the common slots of the expansion, have the same operation at `p`. Both choices are given; no
label at a gate away from `p` is chosen.

Polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`, lines 246–267, 351–381,
409–434 and 565–588. -/
theorem partyOp_partialResidual_all_eq_of_projectAllChoices_eq (w : SourceCircuit X Y) (p : P)
    (ξ ζ : Choices (fun _ ↦ true) w)
    (h : projectAllChoices (partySelector p) w ξ = projectAllChoices (partySelector p) w ζ) :
    PartyCircuit.partyOp (partialResidual (fun _ ↦ true) w ξ) (some ⟨p, rfl⟩) =
      PartyCircuit.partyOp (partialResidual (fun _ ↦ true) w ζ) (some ⟨p, rfl⟩) :=
  partyOp_partialResidual_all_eq_of_incident w p ξ ζ fun g _ hp ↦
    have ht : IsTouched (partySelector p) w g := ⟨p, hp, by simp⟩
    (choiceAt_projectAllChoices _ w ξ g ht).symm.trans
      ((congrArg (fun η ↦ choiceAt (partySelector p) w η g ht) h).trans
        (choiceAt_projectAllChoices _ w ζ g ht))

end QuantumCircuit.Party.SourceCircuit
