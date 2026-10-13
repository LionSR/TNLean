/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.IncidentSourceWord
import TNLean.PEPS.Approximation.AllPartySingletonCircuitComparison
import TNLean.PEPS.Approximation.WordStructuralCongruence

/-!
# The prepared source operator determined by incident labels

For a genuine all-party choice, the selected source-to-output operator equals
the word constructed directly from that party's incident labels. The proof
compares the actual recorded private preparation and the chronological
residual separately, under the fixed selected source-register identifications.
No extension of incident labels or cancellation of a preparation is used.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 351–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

private theorem restrict_partialResidual_eval_heq (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices A w)
    (f : Option {p : P // A p = true} → Bool) :
    HEq ((partialResidual A w ξ).restrict f (sources_partialResidual A w ξ)).eval
      ((partialWord A w ξ).localPart.restrict f (partialWord A w ξ).sources_localPart).eval := by
  unfold partialResidual Word.residualInSlots
  exact Word.restrict_castInput_eval_heq f _ _ _

private theorem restrict_privatePreparation_mapOwner_eval_heq {Q : Type}
    (f : P → Q) (p : P) (q : Q) (hf : ∀ r, f r = q ↔ r = p)
    {a : Layout P} (ψ : ProductInput a) :
    HEq ((ψ.prepare.mapOwner f).restrict (partySelector q)
      (by simp only [Word.sources_mapOwner, ψ.sources_prepare, SourceInventory.mapOwner_nil])).eval
      (ψ.prepare.restrict (partySelector p) ψ.sources_prepare).eval := by
  have hsel : (fun r ↦ partySelector q (f r)) = partySelector p := by
    funext r
    apply Bool.eq_iff_iff.mpr
    simpa only [partySelector, decide_eq_true_eq] using hf r
  have h := Word.restrict_mapOwner_heq f (partySelector q) ψ.prepare ψ.sources_prepare
  rw [hsel] at h
  have hi : Layout.restrict (partySelector q) (Layout.mapOwner f []) =
      Layout.mapOwner f (Layout.restrict (partySelector p) []) := rfl
  have ho : Layout.restrict (partySelector q) (Layout.mapOwner f a) =
      Layout.mapOwner f (Layout.restrict (partySelector p) a) := by
    rw [Layout.restrict_mapOwner, hsel]
  exact (Word.eval_heq hi ho h).trans (Word.eval_mapOwner_heq f _)

/-- Restrict a source-free framed word and then change its owners. The
comparison is proved before the original private preparation is supplied.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 409–434 and 565–588. -/
private theorem restrict_frameList_mapOwner_eval_heq {R Q : Type}
    (f : R → Bool) (lift : R → Q) (S : Layout R) {a b : Layout R}
    (u : Word a b) (hu : u.sources = []) :
    HEq (((Word.frameList S u).restrict f
      ((Word.sources_frameList u S).trans hu)).mapOwner lift).eval
      (Word.frameList (Layout.mapOwner lift (Layout.restrict f S))
        ((u.restrict f hu).mapOwner lift)).eval := by
  have hframe := Word.restrict_frameList_eval_heq f S u hu
  have hMap := (Word.eval_mapOwner_heq lift
      ((Word.frameList S u).restrict f ((Word.sources_frameList u S).trans hu))).trans
    (hframe.trans (Word.eval_mapOwner_heq lift
      (Word.frameList (Layout.restrict f S) (u.restrict f hu))).symm)
  exact hMap.trans (Word.eval_heq (Layout.mapOwner_append lift _ _)
    (Layout.mapOwner_append lift _ _) (Word.mapOwner_frameList_heq lift _ _))

/-- Compare evaluations of arbitrary chronological words before the source
prefixes or private preparation are substituted.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 409–434 and 565–588. -/
private def preparedWordEvalComparison {Q R : Type} {a b : Layout Q} {c d : Layout R}
    (u : Word a b) (v : Word c d) : Prop := HEq u.eval v.eval

/-- The original private preparation has the same selected operator as its
lifted singleton preparation. No monomial choice occurs in this comparison.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 409–434 and 565–588. -/
private theorem preparedWordEvalComparison_privatePreparation {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ψ : ProductInput a) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
    let lift : Option {t : P // A t = true} → Option {_p : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let S := SourceInventory.slotLayout (partialSlots A w)
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
    let Pa : Word (S ++ []) (S ++ Layout.mapOwner (affectedOwner A) a) :=
      Word.frameList S (ψ.prepare.mapOwner (affectedOwner A))
    let hsPa : Pa.sources = [] := by
      simp only [Pa, Word.sources_frameList, Word.sources_mapOwner, ψ.sources_prepare,
        SourceInventory.mapOwner_nil]
    preparedWordEvalComparison
      ((w.sourcePrivatePreparation ψ).restrict (partySelector qp)
        (sources_sourcePrivatePreparation w ψ))
      ((Pa.restrict (partySelector q) hsPa).mapOwner lift) := by
  classical
  intro A hp q qp lift S Pa hsPa
  let all := affectedOwner (fun _ : P ↦ true)
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
  have hSlots : Layout.mapOwner lift (Layout.restrict sa S) =
      Layout.restrict sq w.allResidualSourceLayout :=
    mapOwner_atParty_partialSlots_eq_allResidualSourceLayout w p
  have hBoundary (L : Layout P) :
      Layout.mapOwner lift (Layout.restrict sa (Layout.mapOwner fa L)) =
        Layout.restrict sq (Layout.mapOwner all L) :=
    mapOwner_selected_originalLayout_eq p L
  have hInner : HEq ((ψ.prepare.mapOwner all).restrict sq
      (by simp only [Word.sources_mapOwner, ψ.sources_prepare,
        SourceInventory.mapOwner_nil])).eval
      (((ψ.prepare.mapOwner fa).restrict sa
        (by simp only [Word.sources_mapOwner, ψ.sources_prepare,
          SourceInventory.mapOwner_nil])).mapOwner lift).eval :=
    (restrict_privatePreparation_mapOwner_eval_heq all p qp hfAll ψ).trans
      ((Word.eval_mapOwner_heq lift _).trans
        (restrict_privatePreparation_mapOwner_eval_heq fa p q hfA ψ)).symm
  have hPaMapped : HEq ((Pa.restrict sa hsPa).mapOwner lift).eval
      (Word.frameList (Layout.mapOwner lift (Layout.restrict sa S))
        (((ψ.prepare.mapOwner fa).restrict sa
          (by simp only [Word.sources_mapOwner, ψ.sources_prepare,
            SourceInventory.mapOwner_nil])).mapOwner lift)).eval :=
    restrict_frameList_mapOwner_eval_heq sa lift S (ψ.prepare.mapOwner fa)
      (by simp only [Word.sources_mapOwner, ψ.sources_prepare, SourceInventory.mapOwner_nil])
  have hPrep := (Word.restrict_frameList_eval_heq sq w.allResidualSourceLayout
    (ψ.prepare.mapOwner all)
    (by simp only [Word.sources_mapOwner, ψ.sources_prepare, SourceInventory.mapOwner_nil])).trans
      ((Word.eval_frameList_heq _ _ rfl (hBoundary a).symm hInner
        (Layout.restrict sq w.allResidualSourceLayout)
        (Layout.mapOwner lift (Layout.restrict sa S)) hSlots.symm).trans hPaMapped.symm)
  exact hPrep

/-- Compare a restricted source-free word with a word on its selected
input and output lists, retaining the source-free proof with its word.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 409–434 and 565–588. -/
private def selectedPreparedWordComparison {Q : Type} {a b : Layout Q}
    (f : Q → Bool) (u : Word a b) (hu : u.sources = [])
    (v : Word (Layout.restrict f a) (Layout.restrict f b)) : Prop :=
  (u.restrict f hu).eval = v.eval

/-- The preparation and residual comparisons are combined with a canonical
word comparison as target, before its concrete operator equality is exposed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 351–434 and 565–588. -/
private theorem selectedPreparedWordComparison_of_original_labels {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ψ : ProductInput a)
    (ξ : Choices (fun _ : P ↦ true) w) :
    selectedPreparedWordComparison
      (partySelector (some (⟨p, rfl⟩ : {_p : P // true = true})))
      (w.partialSourceWord ψ ξ) (sources_partialSourceWord w ψ ξ)
      (incidentSourceWord w p ψ (originalGateLabelsAtOfAllChoices w p ξ)) := by
  classical
  let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
    (affectedOwner (fun _ : P ↦ true) t)
  let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
    (decide_eq_true rfl)
  let q : Option {t : P // A t = true} := some ⟨p, hp⟩
  let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
  let lift : Option {t : P // A t = true} → Option {_p : P // true = true} :=
    fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
  let all := affectedOwner (fun _ : P ↦ true)
  let fa := affectedOwner A
  let sq := partySelector qp
  let sa := partySelector q
  let χ := projectAllChoices A w ξ
  let S := SourceInventory.slotLayout (partialSlots A w)
    (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
    (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
  let Pa : Word (S ++ []) (S ++ Layout.mapOwner fa a) :=
    Word.frameList S (ψ.prepare.mapOwner fa)
  have hsPa : Pa.sources = [] := by
    simp only [Pa, Word.sources_frameList, Word.sources_mapOwner, ψ.sources_prepare,
      SourceInventory.mapOwner_nil]
  let Va := Pa.comp (partialResidual A w χ)
  have hsVa : Va.sources = [] := by
    simp only [Va, Word.sources, sources_partialResidual, hsPa, List.nil_append]
  have hSlots : Layout.mapOwner lift (Layout.restrict sa S) =
      Layout.restrict sq w.allResidualSourceLayout :=
    mapOwner_atParty_partialSlots_eq_allResidualSourceLayout w p
  have hBoundary (L : Layout P) :
      Layout.mapOwner lift (Layout.restrict sa (Layout.mapOwner fa L)) =
        Layout.restrict sq (Layout.mapOwner all L) :=
    mapOwner_selected_originalLayout_eq p L
  have hPrep : preparedWordEvalComparison
      ((w.sourcePrivatePreparation ψ).restrict sq (sources_sourcePrivatePreparation w ψ))
      ((Pa.restrict sa hsPa).mapOwner lift) :=
    preparedWordEvalComparison_privatePreparation w p ψ
  have hResidualA := restrict_partialResidual_eval_heq A w χ sa
  have hResidualMapped := (Word.eval_mapOwner_heq lift
    ((partialResidual A w χ).restrict sa (sources_partialResidual A w χ))).trans
      (hResidualA.trans (Word.eval_mapOwner_heq lift
        ((partialWord A w χ).localPart.restrict sa
          (partialWord A w χ).sources_localPart)).symm)
  have hResidual := (restrict_partialResidual_eval_heq (fun _ : P ↦ true) w ξ sq).trans
    ((restrict_partialWord_all_localPart_eval_heq_singleton_projection w p ξ).trans
      hResidualMapped.symm)
  have hin : Layout.restrict sq (w.allResidualSourceLayout ++ []) =
      Layout.mapOwner lift (Layout.restrict sa (S ++ [])) := by
    simpa only [List.append_nil] using hSlots.symm
  have hmid : Layout.restrict sq
      (w.allResidualSourceLayout ++ Layout.mapOwner all a) =
      Layout.mapOwner lift (Layout.restrict sa (S ++ Layout.mapOwner fa a)) := by
    simp only [Layout.restrict_append, Layout.mapOwner_append]
    exact congrArg₂ List.append hSlots.symm (hBoundary a).symm
  have hComp := Word.eval_comp_heq
    ((w.sourcePrivatePreparation ψ).restrict sq (sources_sourcePrivatePreparation w ψ))
    ((partialResidual (fun _ : P ↦ true) w ξ).restrict sq
      (sources_partialResidual (fun _ : P ↦ true) w ξ))
    ((Pa.restrict sa hsPa).mapOwner lift)
    (((partialResidual A w χ).restrict sa (sources_partialResidual A w χ)).mapOwner lift)
    hin hmid (hBoundary b).symm hPrep hResidual
  have hIncident : HEq
      (incidentSourceWord w p ψ (originalGateLabelsAtOfAllChoices w p ξ)).eval
      ((Va.restrict sa hsVa).mapOwner lift).eval := by
    unfold incidentSourceWord
    dsimp only
    rw [choicesOfOriginalGateLabelsAt_eq_projectAllChoices]
    exact Word.eval_castLayouts_heq _ _ _
  apply eq_of_heq
  exact hComp.trans hIncident.symm

/-- The source-to-output operator selected at one party of a genuine all-party
branch is exactly the operator constructed from its original incident labels.
The input is the recorded private product preparation, and the source and
output registers are the actual selected all-party lists. No global extension
of incident labels or additional condition on source vectors is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 351–434 and 565–588. -/
theorem restrict_partialSourceWord_eval_eq_incidentSourceWord {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ψ : ProductInput a)
    (ξ : Choices (fun _ : P ↦ true) w) :
    ((w.partialSourceWord ψ ξ).restrict (partySelector (some ⟨p, rfl⟩))
      (sources_partialSourceWord w ψ ξ)).eval =
      (incidentSourceWord w p ψ (originalGateLabelsAtOfAllChoices w p ξ)).eval := by
  exact selectedPreparedWordComparison_of_original_labels w p ψ ξ

end TNLean.PEPS.PairEffect.SourceCircuit
