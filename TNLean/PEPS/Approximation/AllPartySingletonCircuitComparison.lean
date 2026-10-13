/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AllPartySingletonComparison
import TNLean.PEPS.Approximation.SelectedPartialSourceSlots
import TNLean.PEPS.Approximation.LocalPartRestrictionCongruence

/-!
# A selected party in the singleton and all-party expansions

The chronological remaining operator at one original party agrees between a
genuine all-party choice and its singleton projection. The comparison retains
the original selected source registers, including their order and dimensions.
Only incident gates request labels in the singleton expansion. The proof
compares selected chronological constructors and does not extend incident
labels or restrict an equality of complete operators.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

private theorem projectAllChoices_comp (A : P → Bool) {a b c : Layout P}
    (w : SourceCircuit a b) (v : SourceCircuit b c)
    (ξ : Choices (fun _ ↦ true) (w.comp v)) :
    projectAllChoices A (w.comp v) ξ =
      (projectAllChoices A w ξ.1, projectAllChoices A v ξ.2) := by
  rfl

private theorem projectAllChoices_frame (A : P → Bool) (r : Reg P)
    {a b : Layout P} (w : SourceCircuit a b)
    (ξ : Choices (fun _ ↦ true) (.frame r w)) :
    projectAllChoices A (.frame r w) ξ = projectAllChoices A w ξ := by
  rfl

/-- The selected remaining operator of a genuine all-party branch agrees with
the lifted selected remaining operator of its actual singleton projection.
The source inventory, original dimensions and chronological order are those
of the given circuit. Empty participant and branch sets and zero maps are
included; no extension of incident labels is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
theorem restrict_partialWord_all_localPart_eval_heq_singleton_projection
    {a b : Layout P} (w : SourceCircuit a b) (p : P)
    (ξ : Choices (fun _ : P ↦ true) w) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let χ := projectAllChoices A w ξ
    let W := partialWord (fun _ : P ↦ true) w ξ
    let V := partialWord A w χ
    HEq (W.localPart.restrict (partySelector (some (⟨p, rfl⟩ : {_p : P // true = true})))
      W.sources_localPart).eval
      ((V.localPart.restrict (partySelector q) V.sources_localPart).mapOwner lift).eval := by
  classical
  intro A hp q lift χ W V
  let all := affectedOwner (fun _ : P ↦ true)
  let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
  let fa := affectedOwner A
  let sq := partySelector qp
  let sa := partySelector q
  have hfAll : ∀ r, all r = qp ↔ r = p := by
    intro r
    simp [all, qp, affectedOwner]
  have hfA : ∀ r, fa r = q ↔ r = p := by
    intro r
    simpa only [fa, q, affectedOwner, hp, ↓reduceDIte,
      Bool.true_eq_false, and_false, or_false] using affectedOwner_eq_iff A r p
  have hfLift : ∀ o, lift o = qp ↔ o = q := by
    intro o
    cases o with
    | none => simp [lift, qp, q]
    | some r => simp [lift, qp, q, Subtype.ext_iff]
  have hselectLift : (fun o ↦ sq (lift o)) = sa := by
    funext o
    apply Bool.eq_iff_iff.mpr
    simpa only [sq, sa, partySelector, decide_eq_true_eq] using hfLift o
  have hBoundary (L : Layout P) :
      Layout.restrict sq (Layout.mapOwner all L) =
        Layout.restrict sq (Layout.mapOwner lift (Layout.mapOwner fa L)) := by
    rw [Layout.restrict_mapOwner lift sq (Layout.mapOwner fa L), hselectLift]
    exact (mapOwner_selected_originalLayout_eq p L).symm
  have hSources {a b : Layout P} (v : SourceCircuit a b)
      (η : Choices (fun _ : P ↦ true) v) :
      Layout.restrict sq (partialWord (fun _ : P ↦ true) v η).sources.layout =
        Layout.restrict sq
          ((partialWord A v (projectAllChoices A v η)).mapOwner lift).sources.layout := by
    let Va := partialWord A v (projectAllChoices A v η)
    have hOne := slotLayout_partialSlots_eq A v (projectAllChoices A v η)
    have hAll := slotLayout_partialSlots_eq (fun _ : P ↦ true) v η
    have hSlots := mapOwner_atParty_partialSlots_eq_allResidualSourceLayout v p
    have hSelected : Layout.restrict sq (partialWord (fun _ : P ↦ true) v η).sources.layout =
        Layout.mapOwner lift (Layout.restrict sa Va.sources.layout) := by
      rw [← hAll, ← hOne]
      exact hSlots.symm
    have hLift : Layout.restrict sq (Va.mapOwner lift).sources.layout =
        Layout.mapOwner lift (Layout.restrict sa Va.sources.layout) := by
      rw [Word.sources_mapOwner]
      exact SourceInventory.atParty_layout_mapOwner_of_singleton_fiber
        lift q qp hfLift Va.sources
    exact hSelected.trans hLift.symm
  have hRaw {a b : Layout P} (u : Word a b) :
      HEq ((u.mapOwner all).localPart.restrict sq (u.mapOwner all).sources_localPart).eval
        (((u.mapOwner fa).mapOwner lift).localPart.restrict sq
          ((u.mapOwner fa).mapOwner lift).sources_localPart).eval := by
    let R := u.localPart.restrict (partySelector p) u.sources_localPart
    have hAll := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber
      all p qp hfAll u
    have hOne := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber fa p q hfA u
    have hLift := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber
      lift q qp hfLift (u.mapOwner fa)
    exact hAll.trans ((Word.eval_mapOwner_heq all R).trans
      ((Word.eval_mapOwner_heq fa R).symm.trans
        (hOne.symm.trans
          ((Word.eval_mapOwner_heq lift
            ((u.mapOwner fa).localPart.restrict sa (u.mapOwner fa).sources_localPart)).symm.trans
              hLift.symm))))
  have hCompare {a b : Layout P} (v : SourceCircuit a b)
      (η : Choices (fun _ : P ↦ true) v) :
      HEq ((partialWord (fun _ : P ↦ true) v η).localPart.restrict sq
        (partialWord (fun _ : P ↦ true) v η).sources_localPart).eval
        (((partialWord A v (projectAllChoices A v η)).mapOwner lift).localPart.restrict sq
          ((partialWord A v (projectAllChoices A v η)).mapOwner lift).sources_localPart).eval := by
    induction v generalizing η with
    | id => exact hRaw (Word.id _)
    | localMap r ha hb T tail => exact hRaw (Word.localMap r ha hb T tail)
    | swap r s tail => exact hRaw (Word.swap r s tail)
    | @gate C ι _ _ owner a b c G tail =>
        have hGate := restrict_partialWord_all_gate_localPart_eval_heq_singleton_projection
          owner G tail p η
        have hLift := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber
          lift q qp hfLift (partialWord A (.gate owner G tail)
            (projectAllChoices A (.gate owner G tail) η))
        exact hGate.trans hLift.symm
    | @comp a b c v z ihv ihz =>
        rw [projectAllChoices_comp]
        exact Word.restrict_localPart_comp_eval_heq sq
          (partialWord (fun _ : P ↦ true) v η.1)
          (partialWord (fun _ : P ↦ true) z η.2)
          ((partialWord A v (projectAllChoices A v η.1)).mapOwner lift)
          ((partialWord A z (projectAllChoices A z η.2)).mapOwner lift)
          (hBoundary a) (hBoundary b) (hBoundary c)
          (hSources v η.1) (hSources z η.2) (ihv η.1) (ihz η.2)
    | @frame r a b v ih =>
        rw [projectAllChoices_frame]
        let Va := partialWord A v (projectAllChoices A v η)
        let Vall := partialWord (fun _ : P ↦ true) v η
        let ra : Reg (Option {_p : P // true = true}) := ⟨lift (fa r.owner), r.space⟩
        let rall : Reg (Option {_p : P // true = true}) := ⟨all r.owner, r.space⟩
        by_cases hr : r.owner = p
        · have he : rall = ra := by
            simp [rall, ra, all, fa, lift, affectedOwner, hr, hp]
          change HEq ((Word.frame rall Vall).localPart.restrict sq
            (Word.frame rall Vall).sources_localPart).eval
            ((Word.frame ra (Va.mapOwner lift)).localPart.restrict sq
              (Word.frame ra (Va.mapOwner lift)).sources_localPart).eval
          rw [← he]
          exact Word.restrict_localPart_frame_eval_heq sq rall Vall (Va.mapOwner lift)
            (hBoundary a) (hBoundary b) (hSources v η) (ih η)
        · have hFalseAll : sq rall.owner = false := by
            simp [sq, rall, all, qp, partySelector, affectedOwner, hr]
          have hFalseA : sq ra.owner = false := by
            simp [sq, ra, fa, lift, qp, A, partySelector_affectedOwner_all_apply,
              partySelector, affectedOwner, hr]
          change HEq ((Word.frame rall Vall).localPart.restrict sq
            (Word.frame rall Vall).sources_localPart).eval
            ((Word.frame ra (Va.mapOwner lift)).localPart.restrict sq
              (Word.frame ra (Va.mapOwner lift)).sources_localPart).eval
          exact (Word.restrict_localPart_frame_false_eval_heq sq rall Vall hFalseAll).trans
            ((ih η).trans (Word.restrict_localPart_frame_false_eval_heq sq ra
              (Va.mapOwner lift) hFalseA).symm)
  have h := hCompare w ξ
  have hLift := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber
    lift q qp hfLift V
  exact h.trans hLift

end TNLean.PEPS.PairEffect.SourceCircuit
