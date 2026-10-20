/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.AllPartySingletonComparison
import TNLean.Lattice.Compression.SelectedPartialSourceSlots
import TNLean.Lattice.Compression.SourceResidualCoordinates
import TNLean.Lattice.Compression.LocalPartRestrictionCongruence

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

/-- The selected remaining evaluations of two words are compared with each
source-freeness proof supplied by its own word. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 351–434 and 565–588. -/
private def selectedLocalPartComparison {Q : Type}
    {a b c d : Layout Q} (f : Q → Bool) (u : Word a b) (v : Word c d) : Prop :=
  Word.IsSelectedLocalPartComparison f u v

/-- Two changes of owners with one common singleton original fibre give the
same selected remaining evaluation after lifting the second word.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
private theorem selectedLocalPartComparison_mapOwner {Q R : Type}
    (f : P → Q) (g : P → R) (lift : R → Q) (p : P) (q : Q) (r : R)
    (hf : ∀ z, f z = q ↔ z = p) (hg : ∀ z, g z = r ↔ z = p)
    (hlift : ∀ z, lift z = q ↔ z = r) {a b : Layout P} (u : Word a b) :
    selectedLocalPartComparison (partySelector q) (u.mapOwner f)
      ((u.mapOwner g).mapOwner lift) := by
  unfold selectedLocalPartComparison
  let T := u.localPart.restrict (partySelector p) u.sources_localPart
  have hF := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber f p q hf u
  have hG := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber g p r hg u
  have hLift := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber
    lift r q hlift (u.mapOwner g)
  exact hF.trans ((Word.eval_mapOwner_heq f T).trans
    ((Word.eval_mapOwner_heq g T).symm.trans
      (hG.symm.trans
        ((Word.eval_mapOwner_heq lift
          ((u.mapOwner g).localPart.restrict (partySelector r)
            (u.mapOwner g).sources_localPart)).symm.trans hLift.symm))))

/-- The single-gate comparison is lifted before its application to the
chronological circuit induction. All branch choices and source dimensions
are those of the original gate.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
private theorem selectedLocalPartComparison_gate {C ι : Type} [Fintype C] [Fintype ι]
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) (p : P)
    (ξ : Choices (fun _ : P ↦ true) (.gate owner G tail)) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let _q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {_t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let χ := projectAllChoices A (.gate owner G tail) ξ
    let W := partialWord (fun _ : P ↦ true) (.gate owner G tail) ξ
    let V := partialWord A (.gate owner G tail) χ
    selectedLocalPartComparison (partySelector (some (⟨p, rfl⟩ : {_p : P // true = true})))
      W (V.mapOwner lift) := by
  exact isSelectedLocalPartComparison_partialWord_all_gate owner G tail p ξ

/-- Equal framing registers preserve the comparison of selected remaining
operations when the selected boundary and source lists agree.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267,
351–381 and 409–434. -/
private theorem isSelectedLocalPartComparison_frame_of_eq {Q : Type}
    (f : Q → Bool) (r s : Reg Q) {a b c d : Layout Q}
    (u : Word a b) (v : Word c d) (hrs : r = s)
    (ha : Layout.restrict f a = Layout.restrict f c)
    (hb : Layout.restrict f b = Layout.restrict f d)
    (hs : Layout.restrict f u.sources.layout = Layout.restrict f v.sources.layout)
    (h : Word.IsSelectedLocalPartComparison f u v) :
    Word.IsSelectedLocalPartComparison f (Word.frame r u) (Word.frame s v) := by
  cases hrs
  exact Word.restrict_localPart_frame_eval_heq f r u v ha hb hs h

/-- Framing registers outside the selection preserves the comparison of
selected remaining operations, without comparing the unselected registers.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267,
351–381 and 409–434. -/
private theorem isSelectedLocalPartComparison_frame_of_false {Q : Type}
    (f : Q → Bool) (r s : Reg Q) {a b c d : Layout Q}
    (u : Word a b) (v : Word c d) (hr : f r.owner = false) (hs : f s.owner = false)
    (h : Word.IsSelectedLocalPartComparison f u v) :
    Word.IsSelectedLocalPartComparison f (Word.frame r u) (Word.frame s v) := by
  exact (Word.restrict_localPart_frame_false_eval_heq f r u hr).trans
    (h.trans (Word.restrict_localPart_frame_false_eval_heq f s v hs).symm)

/-- The comparison of the lifted word gives the comparison with lifting
after restriction. This conversion is made with both words arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434
and 565–588. -/
private theorem selectedRemainingComparison_of_selectedLocalPartComparison {Q R : Type}
    (lift : R → Q) (r : R) (q : Q) (hlift : ∀ z, lift z = q ↔ z = r)
    {a b : Layout Q} {c d : Layout R} (u : Word a b) (v : Word c d)
    (h : selectedLocalPartComparison (partySelector q) u (v.mapOwner lift)) :
    HEq (u.localPart.restrict (partySelector q) u.sources_localPart).eval
      ((v.localPart.restrict (partySelector r) v.sources_localPart).mapOwner lift).eval := by
  have hLift := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber
    lift r q hlift v
  exact h.trans hLift

/-- The chronological induction compares words through the canonical
selected-operation proposition before the final owner-lifting conversion.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
private theorem selectedLocalPartComparison_circuit
    {a b : Layout P} (w : SourceCircuit a b) (p : P)
    (ξ : Choices (fun _ : P ↦ true) w) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let _q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {_t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let χ := projectAllChoices A w ξ
    let W := partialWord (fun _ : P ↦ true) w ξ
    let V := partialWord A w χ
    selectedLocalPartComparison
      (partySelector (some (⟨p, rfl⟩ : {_p : P // true = true}))) W (V.mapOwner lift) := by
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
  have hCompare {a b : Layout P} (v : SourceCircuit a b)
      (η : Choices (fun _ : P ↦ true) v) :
      selectedLocalPartComparison sq (partialWord (fun _ : P ↦ true) v η)
        ((partialWord A v (projectAllChoices A v η)).mapOwner lift) := by
    induction v with
    | id a =>
        simpa only [partialWord, Word.mapOwner, sq] using
          selectedLocalPartComparison_mapOwner (affectedOwner (fun _ : P ↦ true))
            (affectedOwner A) lift p qp q hfAll hfA hfLift (Word.id a)
    | localMap r ha hb T tail =>
        simpa only [partialWord, sq] using
          selectedLocalPartComparison_mapOwner (affectedOwner (fun _ : P ↦ true))
            (affectedOwner A) lift p qp q hfAll hfA hfLift (Word.localMap r ha hb T tail)
    | swap r s tail =>
        simpa only [partialWord, sq] using
          selectedLocalPartComparison_mapOwner (affectedOwner (fun _ : P ↦ true))
            (affectedOwner A) lift p qp q hfAll hfA hfLift (Word.swap r s tail)
    | @gate C ι _ _ owner a b c G tail =>
        exact selectedLocalPartComparison_gate owner G tail p η
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
          change selectedLocalPartComparison sq
            (Word.frame rall Vall) (Word.frame ra (Va.mapOwner lift))
          exact isSelectedLocalPartComparison_frame_of_eq sq rall ra Vall (Va.mapOwner lift) he
            (hBoundary a) (hBoundary b) (hSources v η) (ih η)
        · have hFalseAll : sq rall.owner = false := by
            simp [sq, rall, all, qp, partySelector, affectedOwner, hr]
          have hFalseA : sq ra.owner = false := by
            simp [sq, ra, fa, lift, qp, A, partySelector, affectedOwner, hr]
          change selectedLocalPartComparison sq
            (Word.frame rall Vall) (Word.frame ra (Va.mapOwner lift))
          exact isSelectedLocalPartComparison_frame_of_false sq rall ra Vall
            (Va.mapOwner lift) hFalseAll hFalseA (ih η)
  exact hCompare w ξ

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
    let lift : Option {t : P // A t = true} → Option {_t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let χ := projectAllChoices A w ξ
    let W := partialWord (fun _ : P ↦ true) w ξ
    let V := partialWord A w χ
    HEq (W.localPart.restrict (partySelector (some (⟨p, rfl⟩ : {_p : P // true = true})))
      W.sources_localPart).eval
      ((V.localPart.restrict (partySelector q) V.sources_localPart).mapOwner lift).eval := by
  classical
  intro A hp q lift χ W V
  have hlift : ∀ o, lift o = some (⟨p, rfl⟩ : {_p : P // true = true}) ↔ o = q := by
    intro o
    cases o with
    | none => simp [lift, q]
    | some z => simp [lift, q, Subtype.ext_iff]
  exact selectedRemainingComparison_of_selectedLocalPartComparison lift q
    (some (⟨p, rfl⟩ : {_p : P // true = true})) hlift W V
    (selectedLocalPartComparison_circuit w p ξ)

end TNLean.PEPS.PairEffect.SourceCircuit
