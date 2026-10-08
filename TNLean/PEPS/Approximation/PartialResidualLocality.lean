/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ResidualRestrictionCongruence
import TNLean.PEPS.Approximation.AllPartialGate

/-! # Incident choices in the actual chronological expansion

These results concern actual gate occurrences and their selected monomial labels.
Source: polynomial-PEPS, `04-compression.tex`, lines 351–381.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

private theorem localPart_restrict_eval_heq_of_eq {Q : Type} (f : Q → Bool)
    {a b : Layout Q} (w v : Word a b) (h : w = v) :
    HEq ((w.localPart.restrict f w.sources_localPart).eval)
      ((v.localPart.restrict f v.sources_localPart).eval) := by
  cases h
  rfl

set_option maxHeartbeats 800000 in
-- Actual partial words carry nested dependent owner and source-layout transports.
/-- The actual hoisted all-party residual at selected owners depends only on
its incident chronological choices. Empty-participant gates are retained as
whole scalar operations, and no branch label is requested at these gates.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem restrict_partialWord_localPart_eval_heq_of_projectAllChoices_eq
    {a b : Layout P} (w : SourceCircuit a b)
    (f : Option {p : P // (fun _ : P => true) p = true} → Bool)
    (ξ ζ : Choices (fun _ => true) w)
    (h : projectAllChoices (fun p => f (affectedOwner (fun _ => true) p)) w ξ =
      projectAllChoices (fun p => f (affectedOwner (fun _ => true) p)) w ζ) :
    HEq (((partialWord (fun _ => true) w ξ).localPart.restrict f
      (partialWord (fun _ => true) w ξ).sources_localPart).eval)
      (((partialWord (fun _ => true) w ζ).localPart.restrict f
        (partialWord (fun _ => true) w ζ).sources_localPart).eval) := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      exact Word.restrict_localPart_comp_eval_heq f _ _ _ _
        ((layout_partialSlots_eq _ w ξ.1).symm.trans (layout_partialSlots_eq _ w ζ.1))
        ((layout_partialSlots_eq _ v ξ.2).symm.trans (layout_partialSlots_eq _ v ζ.2))
        (ihw ξ.1 ζ.1 (congrArg Prod.fst h)) (ihv ξ.2 ζ.2 (congrArg Prod.snd h))
  | localMap => rfl
  | @gate C ι _ _ owner a b c G tail =>
      classical
      by_cases ht : ∃ _q : C, true = true
      · by_cases hf : ∃ q : C, f (affectedOwner (fun _ => true) (owner q)) = true
        · have hg := (isTouched_gate_iff
            (fun p => f (affectedOwner (fun _ => true) p)) owner G tail).mpr hf
          have he := congrArg (fun η => choiceAt _ (.gate owner G tail) η () hg) h
          have heAll := (choiceAt_projectAllChoices _ (.gate owner G tail) ξ () hg).symm.trans
            (he.trans (choiceAt_projectAllChoices _ (.gate owner G tail) ζ () hg))
          have hξζ : ξ = ζ := by
            dsimp only [choiceAt] at heAll
            exact Equiv.injective _ heAll
          cases hξζ
          rfl
        · have hn : ∀ q : C, f (affectedOwner (fun _ => true) (owner q)) = false := by
            intro q
            exact Bool.eq_false_iff.mpr (fun hq => hf ⟨q, hq⟩)
          exact (restrict_partialWord_all_gate_localPart_eval_heq_id_of_disjoint
            owner G tail ξ ht f hn).trans
              (restrict_partialWord_all_gate_localPart_eval_heq_id_of_disjoint
                owner G tail ζ ht f hn).symm
      · exact localPart_restrict_eval_heq_of_eq f _ _
          (partialWord_all_gate_eq_of_untouched owner G tail ξ ζ ht)
  | swap => rfl
  | frame r w ih =>
      exact Word.restrict_localPart_frame_eval_heq f _ _ _
        ((layout_partialSlots_eq _ w ξ).symm.trans (layout_partialSlots_eq _ w ζ))
        (ih ξ ζ h)

/-- In the fixed source coordinates, the actual all-party residual at selected
owners depends only on its incident chronological choices.
Source: polynomial-PEPS 04-compression.tex, lines 351–381 and 409–434. -/
theorem restrict_partialResidual_eval_eq_of_projectAllChoices_eq
    {a b : Layout P} (w : SourceCircuit a b)
    (f : Option {p : P // (fun _ : P => true) p = true} → Bool)
    (ξ ζ : Choices (fun _ => true) w)
    (h : projectAllChoices (fun p => f (affectedOwner (fun _ => true) p)) w ξ =
      projectAllChoices (fun p => f (affectedOwner (fun _ => true) p)) w ζ) :
    ((partialResidual (fun _ => true) w ξ).restrict f
      (sources_partialResidual _ _ _)).eval =
      ((partialResidual (fun _ => true) w ζ).restrict f
        (sources_partialResidual _ _ _)).eval := by
  unfold partialResidual Word.residualInSlots
  exact eq_of_heq ((Word.restrict_castInput_eval_heq f _ _
    (partialWord (fun _ => true) w ξ).sources_localPart).trans
      ((restrict_partialWord_localPart_eval_heq_of_projectAllChoices_eq w f ξ ζ h).trans
        (Word.restrict_castInput_eval_heq f _ _
          (partialWord (fun _ => true) w ζ).sources_localPart).symm))

end TNLean.PEPS.PairEffect.SourceCircuit
