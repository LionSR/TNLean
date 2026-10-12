/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordPermutationRestriction
import TNLean.PEPS.Approximation.WordEvaluationTransport

/-!
# Restriction of framed local parts

Suppose none of a composition's source registers is selected. Moving those
sources before a list of spectator registers leaves the selected spectators
unchanged. The selected local-part operator is therefore the selected core
operator framed by precisely the retained spectators.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 233–267, 351–381, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Word
open ContinuousLinearMap
variable {P : Type}

/-- If all original source registers are erased, restricting the local part of
a framed composition gives its restricted local part framed by the retained
spectators. The input, output and retained spectator memories are arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
351–381, 409–434 and 565–588. -/
theorem restrict_localPart_frameList_eval_heq (f : P → Bool) (tail : Layout P)
    {a b : Layout P} (w : Word a b) (hs : Layout.restrict f w.sources.layout = []) :
    HEq ((frameList tail w).localPart.restrict f (frameList tail w).sources_localPart).eval
      (frameList (Layout.restrict f tail) (w.localPart.restrict f w.sources_localPart)).eval := by
  induction tail with
  | nil => rfl
  | cons r tail ih =>
      let V := frameList tail w
      let R := frameList (Layout.restrict f (r :: tail))
        (w.localPart.restrict f w.sources_localPart)
      let I := Layout.restrict f (r :: tail) ++
        Layout.restrict f (w.sources.layout ++ a)
      have hV : Layout.restrict f V.sources.layout = [] := by
        simpa only [V, sources_frameList] using hs
      have hi : Layout.restrict f (r :: (tail ++ a)) = I := by
        change Layout.restrict f ((r :: tail) ++ a) =
          Layout.restrict f (r :: tail) ++ Layout.restrict f (w.sources.layout ++ a)
        simp only [Layout.restrict_append, hs, List.nil_append]
      have hm : Layout.restrict f (r :: (V.sources.layout ++ (tail ++ a))) = I := by
        calc
          _ = Layout.restrict f (r :: (tail ++ a)) := by
            simp only [Layout.restrict_cons, Layout.restrict_append, hV, List.nil_append]
          _ = I := hi
      have hmove : HEq
          ((moveHead r V.sources.layout (tail ++ a)).restrict f
            (sources_moveHead r V.sources.layout (tail ++ a))).eval
          (Word.id I).eval :=
        (restrict_moveHead_eval_heq_id_of_prefix_eq_nil f r V.sources.layout
          (tail ++ a) hV).trans
            (eval_id_heq (a := Layout.restrict f (r :: (tail ++ a))) (b := I) hi)
      have hframe : HEq ((Word.frame r V.localPart).restrict f V.sources_localPart).eval
          R.eval := by
        by_cases hr : f r.owner = true
        · have h := (restrict_frame_true_eval_heq f r V.localPart V.sources_localPart hr).trans
            (eval_frame_heq r (V.localPart.restrict f V.sources_localPart)
              (frameList (Layout.restrict f tail)
                (w.localPart.restrict f w.sources_localPart))
              (by simp only [Layout.restrict_append, hV, hs, List.nil_append])
              (Layout.restrict_append f tail b) ih)
          simpa only [R, frameList, Layout.restrict_cons, hr, ↓reduceIte] using h
        · have hr' := Bool.eq_false_iff.mpr hr
          have h := (restrict_frame_false_eval_heq f r V.localPart V.sources_localPart hr').trans ih
          simpa only [R, frameList, Layout.restrict_cons, hr', Bool.false_eq_true,
            ↓reduceIte] using h
      have hcomp := eval_comp_heq
        ((moveHead r V.sources.layout (tail ++ a)).restrict f
          (sources_moveHead r V.sources.layout (tail ++ a)))
        ((Word.frame r V.localPart).restrict f V.sources_localPart) (Word.id I) R
        (by
          calc
            _ = Layout.restrict f (r :: (tail ++ a)) := by
              simp only [Layout.restrict_append, hV, List.nil_append]
            _ = I := hi)
        hm (Layout.restrict_append f (r :: tail) b) hmove hframe
      change HEq (((moveHead r V.sources.layout (tail ++ a)).restrict f
        (sources_moveHead r V.sources.layout (tail ++ a))).comp
          ((Word.frame r V.localPart).restrict f V.sources_localPart)).eval R.eval
      exact hcomp.trans (heq_of_eq (ContinuousLinearMap.comp_id R.eval))

end TNLean.PEPS.PairEffect.Word
