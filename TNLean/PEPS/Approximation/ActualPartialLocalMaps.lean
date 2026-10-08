/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartialResidualLocality

/-! # Incident choices in the actual chronological expansion

These results concern actual gate occurrences and their selected monomial labels.
Source: polynomial-PEPS, `04-compression.tex`, lines 351–381.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- The common input memory of the actual all-party residual.
Source: polynomial-PEPS 04-compression.tex, lines 253–267 and 409–434. -/
abbrev allResidualInput {a b : Layout P} (w : SourceCircuit a b) :
    Layout (Option {p : P // (fun _ : P => true) p = true}) :=
  SourceInventory.slotLayout (partialSlots (fun _ => true) w)
    (fun i => euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1))
    (fun i => euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2)) ++
      Layout.mapOwner (affectedOwner (fun _ => true)) a

/-- A selected residual on the actual incident-choice type. Its value on an
unextendable local choice is zero. Empty-participant gates remain aggregate
operators in the actual all-party expansion, so no labels are requested there.
Source: polynomial-PEPS 04-compression.tex, lines 351–381 and 409–434. -/
def partialLocalRemainingMap {a b : Layout P} (w : SourceCircuit a b)
    (f : Option {p : P // (fun _ : P => true) p = true} → Bool)
    (η : Choices (fun p => f (affectedOwner (fun _ => true) p)) w) :
    Mem (Layout.restrict f w.allResidualInput) →L[ℂ]
      Mem (Layout.restrict f (Layout.mapOwner (affectedOwner (fun _ => true)) b)) := by
  classical
  exact if h : ∃ ξ : Choices (fun _ => true) w,
      projectAllChoices (fun p => f (affectedOwner (fun _ => true) p)) w ξ = η then
    ((partialResidual (fun _ => true) w (Classical.choose h)).restrict f
      (sources_partialResidual _ _ _)).eval
  else 0

set_option maxHeartbeats 800000 in
-- The fixed-source input carries nested dependent layout transports.
/-- The selected map is exactly the restriction of the actual all-party
residual for every genuine chronological choice. No label type is assumed
inhabited. Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem restrict_partialResidual_eq_partialLocalRemainingMap {a b : Layout P}
    (w : SourceCircuit a b)
    (f : Option {p : P // (fun _ : P => true) p = true} → Bool)
    (ξ : Choices (fun _ => true) w) :
    ((partialResidual (fun _ => true) w ξ).restrict f
      (sources_partialResidual _ _ _)).eval =
      w.partialLocalRemainingMap f
        (projectAllChoices (fun p => f (affectedOwner (fun _ => true) p)) w ξ) := by
  classical
  unfold partialLocalRemainingMap
  have h : ∃ ζ : Choices (fun _ => true) w,
      projectAllChoices (fun p => f (affectedOwner (fun _ => true) p)) w ζ =
        projectAllChoices (fun p => f (affectedOwner (fun _ => true) p)) w ξ := ⟨ξ, rfl⟩
  rw [dite_eq_left h]
  exact restrict_partialResidual_eval_eq_of_projectAllChoices_eq w f ξ (Classical.choose h)
    (Classical.choose_spec h).symm

/-- Each selected residual derived from the allowed circuit is contractive.
This includes the zero value at unextendable local choices.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
theorem norm_partialLocalRemainingMap_le_one {a b : Layout P} (w : SourceCircuit a b)
    (hw : w.IsAllowed)
    (f : Option {p : P // (fun _ : P => true) p = true} → Bool)
    (η : Choices (fun p => f (affectedOwner (fun _ => true) p)) w) :
    ‖w.partialLocalRemainingMap f η‖ ≤ 1 := by
  classical
  unfold partialLocalRemainingMap
  by_cases h : ∃ ξ : Choices (fun _ => true) w,
      projectAllChoices (fun p => f (affectedOwner (fun _ => true) p)) w ξ = η
  · rw [dite_eq_left h]
    exact Word.norm_eval_le_one _
      (Word.isAllowed_restrict _ _ _ (isAllowed_partialResidual _ w hw _))
  · rw [dite_eq_right h]
    simp only [norm_zero, zero_le_one]

end TNLean.PEPS.PairEffect.SourceCircuit
