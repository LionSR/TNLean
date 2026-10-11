/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedSourceComposition
import TNLean.PEPS.Approximation.SourceWordParties

/-! # The exterior restriction of a touched all-party gate

When every original party is selected, a gate with a participating party is
replaced by its chosen branch. All registers and named operations of this branch
have selected owners, so its exterior restriction is the identity on the scalar
memory. No hypothesis on the branch vectors or local operators is required.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 233–251, 351–381 and 409–417.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P C ι : Type} [Fintype C] [Fintype ι]

/-- A touched gate in the actual all-party expansion has the identity as its
exterior restriction after its pair preparations have been moved to the
beginning. The original monomial choice and spectator registers are arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 233–251, 351–381 and 409–417. -/
theorem restrict_partialWord_all_gate_localPart_eval_heq_id
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P)
    (ξ : Choices (fun _ : P ↦ true) (.gate owner G tail)) (hC : Nonempty C) :
    HEq (((partialWord (fun _ : P ↦ true) (.gate owner G tail) ξ).localPart.restrict
      Option.isNone (partialWord (fun _ : P ↦ true)
        (.gate owner G tail) ξ).sources_localPart).eval)
      (ContinuousLinearMap.id ℂ ℂ) := by
  classical
  have ht : ∃ _q : C, true = true := ⟨hC.some, rfl⟩
  have hg (i : ι) :=
    Word.restrict_localPart_mapOwner_eval_heq_id_of_disjoint
      (affectedOwner (fun _ : P ↦ true)) none
      (((G.branchWord i).mapOwner owner).appendTail tail)
      (fun p ↦ by simp [affectedOwner])
  rw [partySelector_none] at hg
  unfold partialWord
  rw [dite_eq_left ht]
  exact hg _

end TNLean.PEPS.PairEffect.SourceCircuit
