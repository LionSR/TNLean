/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartySelector
import TNLean.PEPS.Approximation.SelectedSourceOwnerMap
import TNLean.PEPS.Approximation.WordOwnerRestrictionCommutation
import TNLean.PEPS.Approximation.WordOwnerEvaluation
import TNLean.PEPS.Approximation.SourceFreeLocalPart
import TNLean.PEPS.Approximation.WordPermutationRestriction

/-!
# Remaining operations at an owner with a singleton fibre

At a new owner with exactly one original owner in its fibre, the selected
remaining operations agree with the relabelled original selected remaining
operations. Sources whose endpoints merge are treated as actual local
preparations at erased owners. The proof compares the chronological
constructors and their retained source prefixes, without cancelling a source
preparation or restricting an equality of complete operators.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–434
and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Word
open ContinuousLinearMap
variable {P Q : Type}

private theorem eval_mapOwner_of_eval_heq (f : P → Q) {a b a' b' : Layout P}
    (w : Word a b) (v : Word a' b')
    (h : HEq w.eval v.eval) : HEq (w.mapOwner f).eval (v.mapOwner f).eval := by
  exact (eval_mapOwner_heq f w).trans (h.trans (eval_mapOwner_heq f v).symm)

private theorem restrict_eval_of_word_heq (g : Q → Bool) {a b a' b' : Layout Q}
    (w : Word a b) (v : Word a' b') (ha : a = a') (hb : b = b')
    (h : HEq w v) (hs : w.sources = []) (ht : v.sources = []) :
    HEq (w.restrict g hs).eval (v.restrict g ht).eval := by
  cases ha
  cases hb
  cases h
  rfl

private theorem mapOwner_moveHead_heq (f : P → Q) (r : Reg P)
    (rs tail : Layout P) :
    HEq ((moveHead r rs tail).mapOwner f)
      (moveHead ⟨f r.owner, r.space⟩ (Layout.mapOwner f rs) (Layout.mapOwner f tail)) := by
  induction rs with
  | nil => rfl
  | cons s rs ih =>
      let r' : Reg Q := ⟨f r.owner, r.space⟩
      let s' : Reg Q := ⟨f s.owner, s.space⟩
      exact comp_heq
        (congrArg (s' :: ·) (Layout.mapOwner_append f rs (r :: tail)))
        (congrArg (s' :: ·) (congrArg (r' :: ·) (Layout.mapOwner_append f rs tail)))
        (congrArg (r' :: ·) (congrArg (s' :: ·) (Layout.mapOwner_append f rs tail)))
        (frame_heq s' (Layout.mapOwner_append f rs (r :: tail))
          (congrArg (r' :: ·) (Layout.mapOwner_append f rs tail)) ih)
        (swap_heq s' r' (Layout.mapOwner_append f rs tail))

private theorem eval_mapOwner_restrict_frameList (f : P → Q) (g : P → Bool)
    (rs : Layout P) {a b : Layout P} (w : Word a b) (hs : w.sources = []) :
    HEq (((frameList rs w).restrict g ((sources_frameList w rs).trans hs)).mapOwner f).eval
      (frameList (Layout.mapOwner f (Layout.restrict g rs))
        ((w.restrict g hs).mapOwner f)).eval := by
  have h := eval_mapOwner_of_eval_heq f
    ((frameList rs w).restrict g ((sources_frameList w rs).trans hs))
    (frameList (Layout.restrict g rs) (w.restrict g hs))
    (restrict_frameList_eval_heq g rs w hs)
  exact h.trans (eval_heq
    (Layout.mapOwner_append f (Layout.restrict g rs) (Layout.restrict g a))
    (Layout.mapOwner_append f (Layout.restrict g rs) (Layout.restrict g b))
    (mapOwner_frameList_heq f _ _))

private theorem eval_mapOwner_restrict_castInput (f : P → Q) (g : P → Bool)
    {a b a' : Layout P} (w : Word a b) (ha : a = a') (hs : w.sources = []) :
    HEq (((w.castInput ha).restrict g ((sources_castInput w ha).trans hs)).mapOwner f).eval
      ((w.restrict g hs).mapOwner f).eval := by
  exact eval_mapOwner_of_eval_heq f _ _
    (restrict_castInput_eval_heq g w ha hs)

private theorem restrict_localPart_castLayouts_eval_heq (g : Q → Bool)
    {a b a' b' : Layout Q} (w : Word a b) (ha : a = a') (hb : b = b') :
    HEq (((w.castLayouts ha hb).localPart).restrict g
      (w.castLayouts ha hb).sources_localPart).eval
      (w.localPart.restrict g w.sources_localPart).eval := by
  cases ha
  cases hb
  rfl

/-- The exact selected local-part identity, kept as one proposition during
constructor induction. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 246–267, 383–434 and 565–588. -/
private def selectedOwnerLocalPartIdentity (f : P → Q) (sp : P → Bool) (sq : Q → Bool)
    {a b : Layout P} (w : Word a b) : Prop :=
  HEq ((w.mapOwner f).localPart.restrict sq (w.mapOwner f).sources_localPart).eval
    ((w.localPart.restrict sp w.sources_localPart).mapOwner f).eval

private theorem sourceFree_selected_localPart (f : P → Q) (p : P) (q : Q)
    (hsel : (fun r ↦ partySelector q (f r)) = partySelector p)
    {a b : Layout P} (w : Word a b) (hs : w.sources = []) :
    selectedOwnerLocalPartIdentity f (partySelector p) (partySelector q) w := by
  unfold selectedOwnerLocalPartIdentity
  have hm : (w.mapOwner f).sources = [] := by
    simp only [sources_mapOwner, hs, SourceInventory.mapOwner_nil]
  have hc := restrict_mapOwner_heq f (partySelector q) w hs
  rw [hsel] at hc
  have hi : Layout.restrict (partySelector q) (Layout.mapOwner f a) =
      Layout.mapOwner f (Layout.restrict (partySelector p) a) := by
    rw [Layout.restrict_mapOwner, hsel]
  have ho : Layout.restrict (partySelector q) (Layout.mapOwner f b) =
      Layout.mapOwner f (Layout.restrict (partySelector p) b) := by
    rw [Layout.restrict_mapOwner, hsel]
  have hl := restrict_localPart_eval_heq_of_sources_nil (partySelector p) w hs
  have hml := eval_mapOwner_of_eval_heq f _ _ hl
  exact (restrict_localPart_eval_heq_of_sources_nil (partySelector q) _ hm).trans
    ((eval_heq hi ho hc).trans hml.symm)

/-- Framing preserves the selected relabelling identity when the retained
source prefixes agree. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 246–267, 383–434 and 565–588. -/
private theorem selected_localPart_frame_eval_heq
    (f : P → Q) (sp : P → Bool) (sq : Q → Bool)
    (hsel : (fun r ↦ sq (f r)) = sp)
    (r : Reg P) {a b : Layout P} (w : Word a b)
    (hS : Layout.restrict sq (w.mapOwner f).sources.layout =
      Layout.mapOwner f (Layout.restrict sp w.sources.layout))
    (he : selectedOwnerLocalPartIdentity f sp sq w) :
    selectedOwnerLocalPartIdentity f sp sq (Word.frame r w) := by
  classical
  unfold selectedOwnerLocalPartIdentity at he ⊢
  let W := w.mapOwner f
  let r' : Reg Q := ⟨f r.owner, r.space⟩
  have hL (L : Layout P) : Layout.restrict sq (Layout.mapOwner f L) =
      Layout.mapOwner f (Layout.restrict sp L) := by
    rw [Layout.restrict_mapOwner, hsel]
  have hI : Layout.restrict sq (W.sources.layout ++ Layout.mapOwner f a) =
      Layout.mapOwner f (Layout.restrict sp (w.sources.layout ++ a)) := by
    calc
      _ = Layout.restrict sq W.sources.layout ++
          Layout.restrict sq (Layout.mapOwner f a) := Layout.restrict_append sq _ _
      _ = Layout.mapOwner f (Layout.restrict sp w.sources.layout) ++
          Layout.mapOwner f (Layout.restrict sp a) :=
        congrArg₂ (fun S T : Layout Q ↦ S ++ T) hS (hL a)
      _ = Layout.mapOwner f
          (Layout.restrict sp w.sources.layout ++ Layout.restrict sp a) :=
        (Layout.mapOwner_append f _ _).symm
      _ = _ := congrArg (Layout.mapOwner f) (Layout.restrict_append sp _ _).symm
  have hcomm := restrict_mapOwner_heq f sq (moveHead r w.sources.layout a)
    (sources_moveHead r w.sources.layout a)
  rw [hsel] at hcomm
  have hmoveWord := mapOwner_moveHead_heq f r w.sources.layout a
  have hmoveMap : HEq
      (((moveHead r w.sources.layout a).mapOwner f).restrict sq
        (by simp only [sources_mapOwner, sources_moveHead, SourceInventory.mapOwner_nil])).eval
      ((moveHead r' (Layout.mapOwner f w.sources.layout)
        (Layout.mapOwner f a)).restrict sq
          (sources_moveHead r' (Layout.mapOwner f w.sources.layout)
            (Layout.mapOwner f a))).eval := by
    exact restrict_eval_of_word_heq sq _ _
      (Layout.mapOwner_append f w.sources.layout (r :: a))
      (congrArg (r' :: ·) (Layout.mapOwner_append f w.sources.layout a))
      hmoveWord _ _
  have hprefix : Layout.restrict sq W.sources.layout =
      Layout.restrict sq (Layout.mapOwner f w.sources.layout) :=
    hS.trans (hL w.sources.layout).symm
  have hmove := (restrict_moveHead_eval_heq_of_restrict_eq sq r'
    W.sources.layout (Layout.mapOwner f w.sources.layout)
    (Layout.mapOwner f a) (Layout.mapOwner f a) hprefix rfl).trans
      (hmoveMap.symm.trans (eval_heq
        (hL (w.sources.layout ++ r :: a))
        (hL (r :: (w.sources.layout ++ a))) hcomm))
  have hframe : HEq ((Word.frame r' W.localPart).restrict sq W.sources_localPart).eval
      (((Word.frame r w.localPart).restrict sp w.sources_localPart).mapOwner f).eval := by
    by_cases hr : sp r.owner = true
    · have hr' : sq r'.owner = true := (congrFun hsel r.owner).trans hr
      have hright := eval_mapOwner_of_eval_heq f
        ((Word.frame r w.localPart).restrict sp w.sources_localPart)
        (Word.frame r (w.localPart.restrict sp w.sources_localPart))
        (restrict_frame_true_eval_heq sp r w.localPart w.sources_localPart hr)
      exact (restrict_frame_true_eval_heq sq r' W.localPart W.sources_localPart hr').trans
        ((eval_frame_heq r' (W.localPart.restrict sq W.sources_localPart)
          ((w.localPart.restrict sp w.sources_localPart).mapOwner f)
          hI (hL b) he).trans hright.symm)
    · have hr0 := Bool.eq_false_iff.mpr hr
      have hr' : sq r'.owner = false := (congrFun hsel r.owner).trans hr0
      have hright := eval_mapOwner_of_eval_heq f
        ((Word.frame r w.localPart).restrict sp w.sources_localPart)
        (w.localPart.restrict sp w.sources_localPart)
        (restrict_frame_false_eval_heq sp r w.localPart w.sources_localPart hr0)
      exact (restrict_frame_false_eval_heq sq r' W.localPart W.sources_localPart hr').trans
        (he.trans hright.symm)
  have hmid : Layout.restrict sq (r' :: (W.sources.layout ++ Layout.mapOwner f a)) =
      Layout.mapOwner f (Layout.restrict sp (r :: (w.sources.layout ++ a))) := by
    have hr' : sq r'.owner = sp r.owner := congrFun hsel r.owner
    cases hr : sp r.owner with
    | false =>
        simpa only [Layout.restrict_cons, hr', hr, Bool.false_eq_true, ↓reduceIte] using hI
    | true =>
        simpa only [Layout.restrict_cons, hr', hr, ↓reduceIte, Layout.mapOwner_cons] using
          congrArg (r' :: ·) hI
  have hcomp := eval_comp_heq
    ((moveHead r' W.sources.layout (Layout.mapOwner f a)).restrict sq
      (sources_moveHead r' W.sources.layout (Layout.mapOwner f a)))
    ((Word.frame r' W.localPart).restrict sq W.sources_localPart)
    (((moveHead r w.sources.layout a).restrict sp
      (sources_moveHead r w.sources.layout a)).mapOwner f)
    (((Word.frame r w.localPart).restrict sp w.sources_localPart).mapOwner f)
    (by
      calc
        _ = Layout.restrict sq W.sources.layout ++
            Layout.restrict sq (r' :: Layout.mapOwner f a) :=
          Layout.restrict_append sq _ _
        _ = Layout.mapOwner f (Layout.restrict sp w.sources.layout) ++
            Layout.mapOwner f (Layout.restrict sp (r :: a)) :=
          congrArg₂ List.append hS (hL (r :: a))
        _ = _ := by simp only [Layout.restrict_append, Layout.mapOwner_append])
    hmid (hL (r :: b)) hmove hframe
  exact hcomp

/-- Composition preserves the selected relabelling identity under the
retained source-prefix equalities for its two chronological factors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267,
383–434 and 565–588. -/
private theorem selected_localPart_comp_eval_heq
    (f : P → Q) (sp : P → Bool) (sq : Q → Bool)
    (hsel : (fun r ↦ sq (f r)) = sp)
    {a b c : Layout P} (w : Word a b) (v : Word b c)
    (hSw : Layout.restrict sq (w.mapOwner f).sources.layout =
      Layout.mapOwner f (Layout.restrict sp w.sources.layout))
    (hSv : Layout.restrict sq (v.mapOwner f).sources.layout =
      Layout.mapOwner f (Layout.restrict sp v.sources.layout))
    (ihw : selectedOwnerLocalPartIdentity f sp sq w)
    (ihv : selectedOwnerLocalPartIdentity f sp sq v) :
    selectedOwnerLocalPartIdentity f sp sq (w.comp v) := by
  classical
  unfold selectedOwnerLocalPartIdentity at ihw ihv ⊢
  let W := w.mapOwner f
  let V := v.mapOwner f
  have hL (L : Layout P) : Layout.restrict sq (Layout.mapOwner f L) =
      Layout.mapOwner f (Layout.restrict sp L) := by
    rw [Layout.restrict_mapOwner, hsel]
  have hI : Layout.restrict sq (W.sources.layout ++ Layout.mapOwner f a) =
      Layout.mapOwner f (Layout.restrict sp (w.sources.layout ++ a)) := by
    calc
      _ = Layout.restrict sq W.sources.layout ++
          Layout.restrict sq (Layout.mapOwner f a) := Layout.restrict_append sq _ _
      _ = Layout.mapOwner f (Layout.restrict sp w.sources.layout) ++
          Layout.mapOwner f (Layout.restrict sp a) :=
        congrArg₂ (fun S T : Layout Q ↦ S ++ T) hSw (hL a)
      _ = Layout.mapOwner f
          (Layout.restrict sp w.sources.layout ++ Layout.restrict sp a) :=
        (Layout.mapOwner_append f _ _).symm
      _ = _ := congrArg (Layout.mapOwner f) (Layout.restrict_append sp _ _).symm
  have hraw : ((frameList v.sources.layout w.localPart).comp v.localPart).sources = [] := by
    simp only [sources, sources_frameList, sources_localPart, List.nil_append]
  have hraw' : ((frameList V.sources.layout W.localPart).comp V.localPart).sources = [] := by
    simp only [sources, sources_frameList, sources_localPart, List.nil_append]
  have hframe := (restrict_frameList_eval_heq sq V.sources.layout
    W.localPart W.sources_localPart).trans
      ((eval_frameList_heq (W.localPart.restrict sq W.sources_localPart)
        ((w.localPart.restrict sp w.sources_localPart).mapOwner f)
        hI (hL b) ihw (Layout.restrict sq V.sources.layout)
        (Layout.mapOwner f (Layout.restrict sp v.sources.layout)) hSv).trans
          (eval_mapOwner_restrict_frameList f sp v.sources.layout
            w.localPart w.sources_localPart).symm)
  have hcomp := eval_comp_heq
    ((frameList V.sources.layout W.localPart).restrict sq
      ((sources_frameList W.localPart V.sources.layout).trans W.sources_localPart))
    (V.localPart.restrict sq V.sources_localPart)
    (((frameList v.sources.layout w.localPart).restrict sp
      ((sources_frameList w.localPart v.sources.layout).trans w.sources_localPart)).mapOwner f)
    ((v.localPart.restrict sp v.sources_localPart).mapOwner f)
    (by
      calc
        _ = Layout.restrict sq V.sources.layout ++
            Layout.restrict sq (W.sources.layout ++ Layout.mapOwner f a) :=
          Layout.restrict_append sq _ _
        _ = Layout.mapOwner f (Layout.restrict sp v.sources.layout) ++
            Layout.mapOwner f (Layout.restrict sp (w.sources.layout ++ a)) :=
          congrArg₂ (fun S T : Layout Q ↦ S ++ T) hSv hI
        _ = _ := by simp only [Layout.restrict_append, Layout.mapOwner_append])
    (by
      calc
        _ = Layout.restrict sq V.sources.layout ++
            Layout.restrict sq (Layout.mapOwner f b) := Layout.restrict_append sq _ _
        _ = Layout.mapOwner f (Layout.restrict sp v.sources.layout) ++
            Layout.mapOwner f (Layout.restrict sp b) :=
          congrArg₂ (fun S T : Layout Q ↦ S ++ T) hSv (hL b)
        _ = _ := by simp only [Layout.restrict_append, Layout.mapOwner_append])
    (hL c) hframe ihv
  unfold localPart
  exact (restrict_castInput_eval_heq sq _ _ hraw').trans
    (hcomp.trans (eval_mapOwner_restrict_castInput f sp _ _ hraw).symm)

/-- The constructor induction uses the selected source-prefix identity as
an abstract equality for each word. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 246–267, 383–434 and 565–588. -/
private theorem restrict_localPart_mapOwner_eval_heq_induction
    (f : P → Q) (p : P) (q : Q) (hf : ∀ r, f r = q ↔ r = p)
    (hsel : (fun r ↦ partySelector q (f r)) = partySelector p)
    (hS : ∀ {a b : Layout P} (w : Word a b),
      Layout.restrict (partySelector q) (w.mapOwner f).sources.layout =
        Layout.mapOwner f (Layout.restrict (partySelector p) w.sources.layout))
    {a b : Layout P} (u : Word a b) :
    selectedOwnerLocalPartIdentity f (partySelector p) (partySelector q) u := by
  classical
  let sp := partySelector p
  let sq := partySelector q
  have hL (L : Layout P) : Layout.restrict sq (Layout.mapOwner f L) =
      Layout.mapOwner f (Layout.restrict sp L) := by
    rw [Layout.restrict_mapOwner, hsel]
  induction u with
  | id => exact sourceFree_selected_localPart f p q hsel _ rfl
  | localMap => exact sourceFree_selected_localPart f p q hsel _ rfl
  | swap => exact sourceFree_selected_localPart f p q hsel _ rfl
  | @comp a b c w v ihw ihv =>
      exact selected_localPart_comp_eval_heq f sp sq hsel w v (hS w) (hS v) ihw ihv
  | @frame r a b w ih =>
      exact selected_localPart_frame_eval_heq f sp sq hsel r w (hS w) ih
  | @source x y hxy U V η tail =>
      by_cases h : f x = f y
      · have hxq : f x ≠ q := by
          intro hx
          exact hxy (((hf x).mp hx).trans ((hf y).mp (h.symm.trans hx)).symm)
        have hx : x ≠ p := fun hp ↦ hxq ((hf x).mpr hp)
        have hy : y ≠ p := fun hp ↦ hxq (h.trans ((hf y).mpr hp))
        have hcast : (⟨f x, U⟩ :: ⟨f x, V⟩ :: Layout.mapOwner f tail : Layout Q) =
            Layout.mapOwner f (⟨x, U⟩ :: ⟨y, V⟩ :: tail) := by
          simp only [Layout.mapOwner_cons, h]
        have hmap : (Word.source hxy U V η tail).mapOwner f =
            (localPairSource (f x) U V η (Layout.mapOwner f tail)).castLayouts rfl hcast := by
          unfold mapOwner
          exact dite_eq_left h
        have hleft := (restrict_localPart_castLayouts_eval_heq sq
          (localPairSource (f x) U V η (Layout.mapOwner f tail)) rfl hcast).trans
            (restrict_localPart_eval_heq_of_sources_nil sq _ rfl)
        have he : HEq
            (((Word.source hxy U V η tail).mapOwner f).localPart.restrict sq
              ((Word.source hxy U V η tail).mapOwner f).sources_localPart).eval
            (Word.id (Layout.restrict sq (Layout.mapOwner f tail))).eval := by
          rw [hmap]
          exact hleft.trans (restrict_localMap_false_eval_heq sq (f x) _ _ _ _
            (by simp only [sq, partySelector, hxq, decide_false]))
        have hr : HEq
            (((Word.source hxy U V η tail).localPart.restrict sp
              (Word.source hxy U V η tail).sources_localPart).mapOwner f).eval
            (Word.id (Layout.mapOwner f (Layout.restrict sp tail))).eval := by
          apply eval_id_heq
          apply congrArg (Layout.mapOwner f)
          change Layout.restrict sp (⟨x, U⟩ :: ⟨y, V⟩ :: tail) = Layout.restrict sp tail
          simp only [Layout.restrict_cons, sp, partySelector, hx, hy, decide_false,
            Bool.false_eq_true, ↓reduceIte]
        exact he.trans ((eval_id_heq (hL tail)).trans hr.symm)
      · have hmap : (Word.source hxy U V η tail).mapOwner f =
            Word.source h U V η (Layout.mapOwner f tail) := by
          unfold mapOwner
          exact dite_eq_right h
        have hselected := congrArg
          (fun z : Word (Layout.mapOwner f tail)
              (Layout.mapOwner f (⟨x, U⟩ :: ⟨y, V⟩ :: tail)) ↦
            HEq (z.localPart.restrict sq z.sources_localPart).eval
              (((Word.source hxy U V η tail).localPart.restrict sp
                (Word.source hxy U V η tail).sources_localPart).mapOwner f).eval) hmap
        unfold selectedOwnerLocalPartIdentity
        apply Eq.mpr hselected
        change HEq
          (Word.id (Layout.restrict sq
            (Layout.mapOwner f (⟨x, U⟩ :: ⟨y, V⟩ :: tail)))).eval
          (Word.id (Layout.mapOwner f
            (Layout.restrict sp (⟨x, U⟩ :: ⟨y, V⟩ :: tail)))).eval
        exact eval_id_heq (hL (⟨x, U⟩ :: ⟨y, V⟩ :: tail))

/-- At a new owner whose fibre is one original party, the remaining selected
operator is the relabelled remaining operator selected at that original party.
The original word may contain arbitrary pair sources, and owners outside the
selected fibre may merge. This compares the actual local-part constructors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–434
and 565–588. -/
theorem restrict_localPart_mapOwner_eval_heq_of_singleton_fiber
    (f : P → Q) (p : P) (q : Q) (hf : ∀ r, f r = q ↔ r = p)
    {a b : Layout P} (u : Word a b) :
    HEq ((u.mapOwner f).localPart.restrict (partySelector q)
      (u.mapOwner f).sources_localPart).eval
      ((u.localPart.restrict (partySelector p) u.sources_localPart).mapOwner f).eval := by
  classical
  have hsel : (fun r ↦ partySelector q (f r)) = partySelector p := by
    funext r
    apply Bool.eq_iff_iff.mpr
    simpa only [partySelector, decide_eq_true_eq] using hf r
  have hS {a b : Layout P} (w : Word a b) :
      Layout.restrict (partySelector q) (w.mapOwner f).sources.layout =
        Layout.mapOwner f (Layout.restrict (partySelector p) w.sources.layout) := by
    rw [sources_mapOwner]
    exact SourceInventory.atParty_layout_mapOwner_of_singleton_fiber f p q hf w.sources
  change selectedOwnerLocalPartIdentity f (partySelector p) (partySelector q) u
  exact restrict_localPart_mapOwner_eval_heq_induction f p q hf hsel (fun w ↦ hS w) u

end TNLean.PEPS.PairEffect.Word
