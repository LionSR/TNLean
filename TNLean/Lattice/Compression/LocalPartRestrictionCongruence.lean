/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.FrameListRestriction
import TNLean.Lattice.Compression.WordPermutationRestriction
/-!
# Composition of selected remaining operations

Two chronological compositions have the same selected remaining operator
whenever their selected source-register lists agree and their selected
remaining operators agree. Source registers outside the selection need not
coincide. The proof compares the actual later-source framing, composition and
input identifications after restriction, including zero operators.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 246–267, 351–381 and 409–434.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Word
variable {P : Type}

/-- Equal selected input, intermediate, output and source lists, together with
equal already restricted remaining operators, give equal selected remaining
operators after chronological composition. Unselected registers may differ.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267,
351–381 and 409–434. -/
theorem restrict_localPart_comp_eval_heq (f : P → Bool)
    {a b c a' b' c' : Layout P}
    (w : Word a b) (v : Word b c) (w' : Word a' b') (v' : Word b' c')
    (ha : Layout.restrict f a = Layout.restrict f a')
    (hb : Layout.restrict f b = Layout.restrict f b')
    (hc : Layout.restrict f c = Layout.restrict f c')
    (hw : Layout.restrict f w.sources.layout = Layout.restrict f w'.sources.layout)
    (hv : Layout.restrict f v.sources.layout = Layout.restrict f v'.sources.layout)
    (hew : HEq (w.localPart.restrict f w.sources_localPart).eval
      (w'.localPart.restrict f w'.sources_localPart).eval)
    (hev : HEq (v.localPart.restrict f v.sources_localPart).eval
      (v'.localPart.restrict f v'.sources_localPart).eval) :
    HEq ((w.comp v).localPart.restrict f (w.comp v).sources_localPart).eval
      ((w'.comp v').localPart.restrict f (w'.comp v').sources_localPart).eval := by
  have hwi : Layout.restrict f (w.sources.layout ++ a) =
      Layout.restrict f (w'.sources.layout ++ a') := by
    simp only [Layout.restrict_append]
    exact congrArg₂ List.append hw ha
  have hraw : ((frameList v.sources.layout w.localPart).comp v.localPart).sources = [] := by
    simp only [sources, sources_frameList, sources_localPart, List.nil_append]
  have hraw' : ((frameList v'.sources.layout w'.localPart).comp v'.localPart).sources = [] := by
    simp only [sources, sources_frameList, sources_localPart, List.nil_append]
  have hframe := (restrict_frameList_eval_heq f v.sources.layout
    w.localPart w.sources_localPart).trans
      ((eval_frameList_heq (w.localPart.restrict f w.sources_localPart)
        (w'.localPart.restrict f w'.sources_localPart) hwi
        hb hew
        (Layout.restrict f v.sources.layout) (Layout.restrict f v'.sources.layout) hv).trans
          (restrict_frameList_eval_heq f v'.sources.layout
            w'.localPart w'.sources_localPart).symm)
  have hcomp := eval_comp_heq
    ((frameList v.sources.layout w.localPart).restrict f
      ((sources_frameList w.localPart v.sources.layout).trans w.sources_localPart))
    (v.localPart.restrict f v.sources_localPart)
    ((frameList v'.sources.layout w'.localPart).restrict f
      ((sources_frameList w'.localPart v'.sources.layout).trans w'.sources_localPart))
    (v'.localPart.restrict f v'.sources_localPart)
    (by
      simp only [Layout.restrict_append]
      exact congrArg₂ List.append hv
        (congrArg₂ List.append hw ha))
    (by
      simp only [Layout.restrict_append]
      exact congrArg₂ List.append hv hb)
    hc hframe hev
  unfold localPart
  exact (restrict_castInput_eval_heq f _ _ hraw).trans
    (hcomp.trans (restrict_castInput_eval_heq f _ _ hraw').symm)

/-- Framing preserves equality of selected remaining operators when the
selected input, output and source lists agree. Unselected registers may differ,
and no operator is cancelled.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267,
351–381 and 409–434. -/
theorem restrict_localPart_frame_eval_heq (f : P → Bool) (r : Reg P)
    {a b a' b' : Layout P} (w : Word a b) (w' : Word a' b')
    (ha : Layout.restrict f a = Layout.restrict f a')
    (hb : Layout.restrict f b = Layout.restrict f b')
    (hs : Layout.restrict f w.sources.layout = Layout.restrict f w'.sources.layout)
    (he : HEq (w.localPart.restrict f w.sources_localPart).eval
      (w'.localPart.restrict f w'.sources_localPart).eval) :
    HEq ((Word.frame r w).localPart.restrict f (Word.frame r w).sources_localPart).eval
      ((Word.frame r w').localPart.restrict f (Word.frame r w').sources_localPart).eval := by
  have hwi : Layout.restrict f (w.sources.layout ++ a) =
      Layout.restrict f (w'.sources.layout ++ a') := by
    simp only [Layout.restrict_append]
    exact congrArg₂ List.append hs ha
  have hmove := restrict_moveHead_eval_heq_of_restrict_eq f r
    w.sources.layout w'.sources.layout a a' hs ha
  have hframe : HEq ((Word.frame r w.localPart).restrict f w.sources_localPart).eval
      ((Word.frame r w'.localPart).restrict f w'.sources_localPart).eval := by
    by_cases hr : f r.owner = true
    · exact (restrict_frame_true_eval_heq f r w.localPart w.sources_localPart hr).trans
        ((eval_frame_heq r (w.localPart.restrict f w.sources_localPart)
          (w'.localPart.restrict f w'.sources_localPart) hwi
          hb he).trans
            (restrict_frame_true_eval_heq f r w'.localPart w'.sources_localPart hr).symm)
    · have hr' := Bool.eq_false_iff.mpr hr
      exact (restrict_frame_false_eval_heq f r w.localPart w.sources_localPart hr').trans
        (he.trans (restrict_frame_false_eval_heq f r w'.localPart
          w'.sources_localPart hr').symm)
  have hmid : Layout.restrict f (r :: (w.sources.layout ++ a)) =
      Layout.restrict f (r :: (w'.sources.layout ++ a')) := by
    simp only [Layout.restrict_cons]
    rw [hwi]
  have hcomp := eval_comp_heq
    ((moveHead r w.sources.layout a).restrict f (sources_moveHead r w.sources.layout a))
    ((Word.frame r w.localPart).restrict f w.sources_localPart)
    ((moveHead r w'.sources.layout a').restrict f (sources_moveHead r w'.sources.layout a'))
    ((Word.frame r w'.localPart).restrict f w'.sources_localPart)
    (by
      simp only [Layout.restrict_append]
      exact congrArg₂ List.append hs (by
        simp only [Layout.restrict_cons]
        rw [ha]))
    hmid (by
      simp only [Layout.restrict_cons]
      rw [hb]) hmove hframe
  change HEq
    (((moveHead r w.sources.layout a).restrict f
      (sources_moveHead r w.sources.layout a)).comp
        ((Word.frame r w.localPart).restrict f w.sources_localPart)).eval
    (((moveHead r w'.sources.layout a').restrict f
      (sources_moveHead r w'.sources.layout a')).comp
        ((Word.frame r w'.localPart).restrict f w'.sources_localPart)).eval
  exact hcomp

/-- Framing a register outside the selection does not change the selected
remaining operator, even when the original word contains pair sources and
retained source registers. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 246–267, 351–381 and 409–434. -/
theorem restrict_localPart_frame_false_eval_heq (f : P → Bool) (r : Reg P)
    {a b : Layout P} (w : Word a b) (hr : f r.owner = false) :
    HEq ((Word.frame r w).localPart.restrict f (Word.frame r w).sources_localPart).eval
      (w.localPart.restrict f w.sources_localPart).eval := by
  let T := Layout.restrict f (w.sources.layout ++ a)
  let u := (moveHead r w.sources.layout a).restrict f (sources_moveHead r w.sources.layout a)
  let v := (Word.frame r w.localPart).restrict f w.sources_localPart
  let core := w.localPart.restrict f w.sources_localPart
  have hmove : HEq u.eval (Word.id T).eval :=
    (restrict_moveHead_false_eval_heq f r w.sources.layout a hr).trans
      (eval_id_heq (Layout.restrict_append f w.sources.layout a).symm)
  have hframe : HEq v.eval core.eval :=
    restrict_frame_false_eval_heq f r w.localPart w.sources_localPart hr
  have hcomp := eval_comp_heq u v (Word.id T) core
    (by simp only [T, Layout.restrict_append, Layout.restrict_cons,
      hr, Bool.false_eq_true, ↓reduceIte])
    (by simp only [T, Layout.restrict_cons, hr, Bool.false_eq_true, ↓reduceIte])
    (by simp only [Layout.restrict_cons, hr, Bool.false_eq_true, ↓reduceIte])
    hmove hframe
  change HEq (u.comp v).eval core.eval
  exact hcomp.trans (heq_of_eq (ContinuousLinearMap.comp_id core.eval))

end TNLean.PEPS.PairEffect.Word
