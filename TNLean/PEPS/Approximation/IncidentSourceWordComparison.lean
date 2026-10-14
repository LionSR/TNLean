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

/-- Selection of arbitrary source-free words commutes with framing and
owner transport when the retained source and boundary lists agree. The inner
operator comparison is supplied before any original source inventory is fixed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 409–434 and 565–588. -/
private theorem preparedWordEvalComparison_frameList {Q R : Type}
    {a b : Layout Q} {c d : Layout R} (sq : Q → Bool) (sa : R → Bool)
    (lift : R → Q) (Sq : Layout Q) (Sa : Layout R)
    (u : Word a b) (v : Word c d) (hu : u.sources = []) (hv : v.sources = [])
    (hi : Layout.restrict sq a = Layout.mapOwner lift (Layout.restrict sa c))
    (ho : Layout.restrict sq b = Layout.mapOwner lift (Layout.restrict sa d))
    (hS : Layout.restrict sq Sq = Layout.mapOwner lift (Layout.restrict sa Sa))
    (hInner : HEq (u.restrict sq hu).eval ((v.restrict sa hv).mapOwner lift).eval) :
    preparedWordEvalComparison
      ((Word.frameList Sq u).restrict sq ((Word.sources_frameList u Sq).trans hu))
      (((Word.frameList Sa v).restrict sa
        ((Word.sources_frameList v Sa).trans hv)).mapOwner lift) := by
  have hMapped := restrict_frameList_mapOwner_eval_heq sa lift Sa v hv
  have hFramed := Word.eval_frameList_heq (u.restrict sq hu)
    ((v.restrict sa hv).mapOwner lift) hi ho hInner
    (Layout.restrict sq Sq) (Layout.mapOwner lift (Layout.restrict sa Sa)) hS
  exact (Word.restrict_frameList_eval_heq sq Sq u hu).trans
    (hFramed.trans hMapped.symm)

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
  exact preparedWordEvalComparison_frameList sq sa lift w.allResidualSourceLayout S
    (ψ.prepare.mapOwner all) (ψ.prepare.mapOwner fa)
    (by simp only [Word.sources_mapOwner, ψ.sources_prepare, SourceInventory.mapOwner_nil])
    (by simp only [Word.sources_mapOwner, ψ.sources_prepare, SourceInventory.mapOwner_nil])
    rfl (hBoundary a).symm hSlots.symm hInner

/-- Compare a restricted source-free word with a word on its selected
input and output lists, retaining the source-free proof with its word.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 409–434 and 565–588. -/
private def selectedPreparedWordComparison {Q : Type} {a b : Layout Q}
    (f : Q → Bool) (u : Word a b) (hu : u.sources = [])
    (v : Word (Layout.restrict f a) (Layout.restrict f b)) : Prop :=
  (u.restrict f hu).eval = v.eval

/-- Compose two selected source-free word comparisons before any concrete
preparation, residual or incident-label word is substituted.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 351–434 and 565–588. -/
private theorem selectedPreparedWordComparison_comp {Q R : Type}
    {a b c : Layout Q} {d e f : Layout R}
    (sq : Q → Bool) (sa : R → Bool) (lift : R → Q)
    (u : Word a b) (v : Word b c) (x : Word d e) (y : Word e f)
    (hu : u.sources = []) (hv : v.sources = [])
    (hx : x.sources = []) (hy : y.sources = []) (hxy : (x.comp y).sources = [])
    (t : Word (Layout.restrict sq a) (Layout.restrict sq c))
    (hi : Layout.restrict sq a = Layout.mapOwner lift (Layout.restrict sa d))
    (hm : Layout.restrict sq b = Layout.mapOwner lift (Layout.restrict sa e))
    (ho : Layout.restrict sq c = Layout.mapOwner lift (Layout.restrict sa f))
    (hPrep : HEq (u.restrict sq hu).eval ((x.restrict sa hx).mapOwner lift).eval)
    (hResidual : HEq (v.restrict sq hv).eval ((y.restrict sa hy).mapOwner lift).eval)
    (hWord : HEq t (((x.comp y).restrict sa hxy).mapOwner lift)) :
    selectedPreparedWordComparison sq (u.comp v)
      (by simp only [Word.sources, hv, hu, List.nil_append]) t := by
  have hComp := Word.eval_comp_heq (u.restrict sq hu) (v.restrict sq hv)
    ((x.restrict sa hx).mapOwner lift) ((y.restrict sa hy).mapOwner lift)
    hi hm ho hPrep hResidual
  have hTarget := Word.eval_heq hi ho hWord
  apply eq_of_heq
  exact hComp.trans hTarget.symm

/-- Equal source-free words remain equal after selection and owner transport,
under a prescribed identification of their retained register lists.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 351–434 and 565–588. -/
private theorem restrict_mapOwner_castLayouts_heq_of_eq {Q R : Type}
    {a b : Layout Q} {c d : Layout R} (s : Q → Bool) (lift : Q → R)
    (u v : Word a b) (hu : u.sources = []) (hv : v.sources = [])
    (hi : Layout.mapOwner lift (Layout.restrict s a) = c)
    (ho : Layout.mapOwner lift (Layout.restrict s b) = d) (h : u = v) :
    HEq (((u.restrict s hu).mapOwner lift).castLayouts hi ho)
      ((v.restrict s hv).mapOwner lift) := by
  cases h
  exact Word.castLayouts_heq _ hi ho

/-- The literal incident word is the selected and lifted word of the original
preparation and projected residual. All labels and source registers are derived
from the same original all-party choice. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 137–139, 246–267, 351–434 and 565–588. -/
private theorem incidentSourceWord_heq_of_original_labels {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ψ : ProductInput a)
    (ξ : Choices (fun _ : P ↦ true) w) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {_p : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let S := SourceInventory.slotLayout (partialSlots A w)
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
    let χ := projectAllChoices A w ξ
    let Pa : Word (S ++ []) (S ++ Layout.mapOwner (affectedOwner A) a) :=
      Word.frameList S (ψ.prepare.mapOwner (affectedOwner A))
    let hsPa : Pa.sources = [] := by
      simp only [Pa, Word.sources_frameList, Word.sources_mapOwner, ψ.sources_prepare,
        SourceInventory.mapOwner_nil]
    let Va := Pa.comp (partialResidual A w χ)
    let hsVa : Va.sources = [] := by
      simp only [Va, Word.sources, sources_partialResidual, hsPa, List.nil_append]
    HEq (incidentSourceWord w p ψ (originalGateLabelsAtOfAllChoices w p ξ))
      ((Va.restrict (partySelector q) hsVa).mapOwner lift) := by
  classical
  intro A hp q lift S χ Pa hsPa Va hsVa
  let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
  let all := affectedOwner (fun _ : P ↦ true)
  let fa := affectedOwner A
  let sq := partySelector qp
  let sa := partySelector q
  have hSlots : Layout.mapOwner lift (Layout.restrict sa S) =
      Layout.restrict sq w.allResidualSourceLayout :=
    mapOwner_atParty_partialSlots_eq_allResidualSourceLayout w p
  have hBoundary (L : Layout P) :
      Layout.mapOwner lift (Layout.restrict sa (Layout.mapOwner fa L)) =
        Layout.restrict sq (Layout.mapOwner all L) :=
    mapOwner_selected_originalLayout_eq p L
  have hin : Layout.restrict sq (w.allResidualSourceLayout ++ []) =
      Layout.mapOwner lift (Layout.restrict sa (S ++ [])) := by
    simpa only [List.append_nil] using hSlots.symm
  unfold incidentSourceWord
  dsimp only
  exact restrict_mapOwner_castLayouts_heq_of_eq sa lift
    (Pa.comp (partialResidual A w
      (choicesOfOriginalGateLabelsAt w p (originalGateLabelsAtOfAllChoices w p ξ))))
    Va
    (by simp only [Word.sources, sources_partialResidual, hsPa, List.nil_append])
    hsVa hin.symm (hBoundary b)
    (congrArg (fun ζ : Choices A w ↦ Pa.comp (partialResidual A w ζ))
      (choicesOfOriginalGateLabelsAt_eq_projectAllChoices w p ξ))

/-- Compare selected source-free words through the selected local parts
of two arbitrary full words, before original circuit data are substituted.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267,
351–434 and 565–588. -/
private theorem preparedWordEvalComparison_of_localPart {Q R : Type}
    {a b e f : Layout Q} {c d g h : Layout R}
    (sq : Q → Bool) (sa : R → Bool) (lift : R → Q)
    (u : Word a b) (v : Word c d) (W : Word e f) (Z : Word g h)
    (hu : u.sources = []) (hv : v.sources = [])
    (hLeft : HEq (u.restrict sq hu).eval
      (W.localPart.restrict sq W.sources_localPart).eval)
    (hRight : HEq (v.restrict sa hv).eval
      (Z.localPart.restrict sa Z.sources_localPart).eval)
    (hFull : HEq (W.localPart.restrict sq W.sources_localPart).eval
      ((Z.localPart.restrict sa Z.sources_localPart).mapOwner lift).eval) :
    preparedWordEvalComparison (u.restrict sq hu) ((v.restrict sa hv).mapOwner lift) := by
  have hResidualMapped := (Word.eval_mapOwner_heq lift (v.restrict sa hv)).trans
    (hRight.trans (Word.eval_mapOwner_heq lift
      (Z.localPart.restrict sa Z.sources_localPart)).symm)
  exact hLeft.trans (hFull.trans hResidualMapped.symm)

/-- The original all-party residual and its lifted singleton projection
have the same selected operator. All choices are projections of the same
original branch. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 246–267, 351–434 and 565–588. -/
private theorem preparedWordEvalComparison_partialResidual {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ξ : Choices (fun _ : P ↦ true) w) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
    let lift : Option {t : P // A t = true} → Option {_p : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let χ := projectAllChoices A w ξ
    preparedWordEvalComparison
      ((partialResidual (fun _ : P ↦ true) w ξ).restrict (partySelector qp)
        (sources_partialResidual (fun _ : P ↦ true) w ξ))
      (((partialResidual A w χ).restrict (partySelector q)
        (sources_partialResidual A w χ)).mapOwner lift) := by
  classical
  intro A hp q qp lift χ
  let sq := partySelector qp
  let sa := partySelector q
  exact preparedWordEvalComparison_of_localPart sq sa lift
    (partialResidual (fun _ : P ↦ true) w ξ) (partialResidual A w χ)
    (partialWord (fun _ : P ↦ true) w ξ) (partialWord A w χ)
    (sources_partialResidual (fun _ : P ↦ true) w ξ) (sources_partialResidual A w χ)
    (restrict_partialResidual_eval_heq (fun _ : P ↦ true) w ξ sq)
    (restrict_partialResidual_eval_heq A w χ sa)
    (restrict_partialWord_all_localPart_eval_heq_singleton_projection w p ξ)

/-- Compare the original prepared word with its incident-label word, with
all original source and output data fixed before the comparison is proved.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 351–434 and 565–588. -/
private def selectedPreparedOriginalLabelComparison {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ψ : ProductInput a)
    (ξ : Choices (fun _ : P ↦ true) w) : Prop :=
    selectedPreparedWordComparison
      (partySelector (some (⟨p, rfl⟩ : {_p : P // true = true})))
      (w.partialSourceWord ψ ξ) (sources_partialSourceWord w ψ ξ)
      (incidentSourceWord w p ψ (originalGateLabelsAtOfAllChoices w p ξ))

/-- The preparation and residual comparisons are combined with a canonical
word comparison as target, before its concrete operator equality is exposed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267, 351–434 and 565–588. -/
private theorem selectedPreparedWordComparison_of_original_labels {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ψ : ProductInput a)
    (ξ : Choices (fun _ : P ↦ true) w) :
    selectedPreparedOriginalLabelComparison w p ψ ξ := by
  unfold selectedPreparedOriginalLabelComparison
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
  have hResidual : preparedWordEvalComparison
      ((partialResidual (fun _ : P ↦ true) w ξ).restrict sq
        (sources_partialResidual (fun _ : P ↦ true) w ξ))
      (((partialResidual A w χ).restrict sa
        (sources_partialResidual A w χ)).mapOwner lift) :=
    preparedWordEvalComparison_partialResidual w p ξ
  have hin : Layout.restrict sq (w.allResidualSourceLayout ++ []) =
      Layout.mapOwner lift (Layout.restrict sa (S ++ [])) := by
    simpa only [List.append_nil] using hSlots.symm
  have hmid : Layout.restrict sq
      (w.allResidualSourceLayout ++ Layout.mapOwner all a) =
      Layout.mapOwner lift (Layout.restrict sa (S ++ Layout.mapOwner fa a)) := by
    simp only [Layout.restrict_append, Layout.mapOwner_append]
    exact congrArg₂ List.append hSlots.symm (hBoundary a).symm
  have hWord : HEq
      (incidentSourceWord w p ψ (originalGateLabelsAtOfAllChoices w p ξ))
      ((Va.restrict sa hsVa).mapOwner lift) :=
    incidentSourceWord_heq_of_original_labels w p ψ ξ
  exact selectedPreparedWordComparison_comp sq sa lift
    (w.sourcePrivatePreparation ψ) (partialResidual (fun _ : P ↦ true) w ξ)
    Pa (partialResidual A w χ)
    (sources_sourcePrivatePreparation w ψ)
    (sources_partialResidual (fun _ : P ↦ true) w ξ)
    hsPa (sources_partialResidual A w χ) hsVa
    (incidentSourceWord w p ψ (originalGateLabelsAtOfAllChoices w p ξ))
    hin hmid (hBoundary b).symm hPrep hResidual hWord

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
