/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FrameListRestriction
import TNLean.PEPS.Approximation.WordEvaluationTransport

/-!
# Restriction of the local part of a source-free composition

When the source inventory is empty, taking the local part preserves every
selected chronological operator. The proof follows the composition and framing
constructors: source prefixes are empty, and moving a framed register through
an empty source prefix contributes the identity.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 233–267, 351–381 and 409–434.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Word
open ContinuousLinearMap
variable {P : Type}

private theorem restrict_castInput_eval_heq (f : P → Bool) {a b a' : Layout P}
    (w : Word a b) (h : a = a') (hs : w.sources = []) :
    HEq ((w.castInput h).restrict f ((sources_castInput w h).trans hs)).eval
      (w.restrict f hs).eval := by
  cases h
  rfl

private theorem restrict_moveHead_empty_eval_heq (f : P → Bool) (r : Reg P)
    (S a : Layout P) (hS : S = []) :
    HEq ((moveHead r S a).restrict f (sources_moveHead r S a)).eval
      (Word.id (Layout.restrict f (r :: a))).eval := by
  cases hS
  rfl

/-- Taking the local part of a source-free composition preserves its restriction
to any selected owners, under the canonical empty-prefix identification.
The proof compares the chronological constructions themselves. The input and
output memories and the selector are arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
351–381 and 409–434. -/
theorem restrict_localPart_eval_heq_of_sources_nil (f : P → Bool) {a b : Layout P}
    (w : Word a b) (hs : w.sources = []) :
    HEq (w.localPart.restrict f w.sources_localPart).eval (w.restrict f hs).eval := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      have hsw := (List.append_eq_nil_iff.mp hs).2
      have hsv := (List.append_eq_nil_iff.mp hs).1
      have hW : w.sources.layout = [] := by rw [hsw]; rfl
      have hV : v.sources.layout = [] := by rw [hsv]; rfl
      have hraw : ((frameList v.sources.layout w.localPart).comp v.localPart).sources = [] := by
        simp only [sources, sources_frameList, sources_localPart, List.nil_append]
      have hleft := (restrict_frameList_eval_heq_of_eq_nil f v.sources.layout
        (by rw [hV]; rfl) w.localPart w.sources_localPart).trans (ihw hsw)
      have hright := ihv hsv
      unfold localPart
      refine (restrict_castInput_eval_heq f _ _ hraw).trans ?_
      exact eval_comp_heq
        ((frameList v.sources.layout w.localPart).restrict f
          ((sources_frameList w.localPart v.sources.layout).trans w.sources_localPart))
        (v.localPart.restrict f v.sources_localPart) (w.restrict f hsw) (v.restrict f hsv)
        (by simp only [Layout.restrict_append, hW, hV, Layout.restrict_nil, List.nil_append])
        (by simp only [Layout.restrict_append, hV, Layout.restrict_nil, List.nil_append])
        rfl hleft hright
  | localMap => rfl
  | source => cases hs
  | swap => rfl
  | @frame r a b w ih =>
      have hS : w.sources.layout = [] := by rw [hs]; rfl
      have hframe : HEq ((Word.frame r w.localPart).restrict f w.sources_localPart).eval
          ((Word.frame r w).restrict f hs).eval := by
        by_cases hr : f r.owner = true
        · exact (restrict_frame_true_eval_heq f r w.localPart w.sources_localPart hr).trans
            ((eval_frame_heq r (w.localPart.restrict f w.sources_localPart) (w.restrict f hs)
              (by simp only [Layout.restrict_append, hS, Layout.restrict_nil, List.nil_append])
              rfl (ih hs)).trans (restrict_frame_true_eval_heq f r w hs hr).symm)
        · have hr' := Bool.eq_false_iff.mpr hr
          exact (restrict_frame_false_eval_heq f r w.localPart w.sources_localPart hr').trans
            ((ih hs).trans (restrict_frame_false_eval_heq f r w hs hr').symm)
      have hcomp := eval_comp_heq
        ((moveHead r w.sources.layout a).restrict f (sources_moveHead r w.sources.layout a))
        ((Word.frame r w.localPart).restrict f w.sources_localPart)
        (Word.id (Layout.restrict f (r :: a))) ((Word.frame r w).restrict f hs)
        (by simp only [Layout.restrict_append, hS, Layout.restrict_nil, List.nil_append])
        (by rw [hS]; rfl) rfl
        (restrict_moveHead_empty_eval_heq f r w.sources.layout a hS) hframe
      change HEq (((moveHead r w.sources.layout a).restrict f
        (sources_moveHead r w.sources.layout a)).comp
          ((Word.frame r w.localPart).restrict f w.sources_localPart)).eval
        ((Word.frame r w).restrict f hs).eval
      exact hcomp.trans (heq_of_eq (ContinuousLinearMap.comp_id _))

end TNLean.PEPS.PairEffect.Word
