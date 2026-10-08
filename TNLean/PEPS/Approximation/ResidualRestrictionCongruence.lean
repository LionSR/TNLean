/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcefulInvisibleRestriction

/-! # Actual restriction identities in the chronological source construction

These identities concern the actual restricted words and monomial choices.
Source: polynomial-PEPS, `04-compression.tex`, lines 246–251 and 351–381.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-network-residualrestrictioncongruence-01
TNLean.PEPS.PairEffect.Word.restrict_castInput_eval_heq
Provenance-ID: 8769-chronological-network-residualrestrictioncongruence-02
TNLean.PEPS.PairEffect.Word.restrict_comp_eval_heq
Provenance-ID: 8769-chronological-network-residualrestrictioncongruence-03
TNLean.PEPS.PairEffect.Word.restrict_frameList_eval_heq
Provenance-ID: 8769-chronological-network-residualrestrictioncongruence-04
TNLean.PEPS.PairEffect.Word.restrict_frame_eval_heq
Provenance-ID: 8769-chronological-network-residualrestrictioncongruence-05
TNLean.PEPS.PairEffect.Word.restrict_localPart_comp_eval_heq
Provenance-ID: 8769-chronological-network-residualrestrictioncongruence-06
TNLean.PEPS.PairEffect.Word.restrict_localPart_frame_eval_heq
Provenance-ID: 8769-chronological-network-residualrestrictioncongruence-07
TNLean.PEPS.PairEffect.Word.restrict_moveHead_eval_heq
-/


noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P : Type}
namespace Word
/-- Congruence for the actual restricted residual operations.
Source: polynomial-PEPS 04-compression.tex, lines 246–251 and 351–381. -/
theorem restrict_castInput_eval_heq (f : P → Bool) {a b a' : Layout P}
    (w : Word a b) (h : a = a') (hs : w.sources = []) :
    HEq (((w.castInput h).restrict f ((sources_castInput _ _).trans hs)).eval)
      ((w.restrict f hs).eval) := by
  cases h
  rfl

/-- Congruence for the actual restricted residual operations.
Source: polynomial-PEPS 04-compression.tex, lines 246–251 and 351–381. -/
theorem restrict_comp_eval_heq (f : P → Bool) {a b d a' b' d' : Layout P}
    (ha : a = a') (hb : b = b') (hd : d = d')
    (w : Word a b) (w' : Word a' b') (v : Word b d) (v' : Word b' d')
    (hw : w.sources = []) (hw' : w'.sources = [])
    (hv : v.sources = []) (hv' : v'.sources = [])
    (he : HEq ((w.restrict f hw).eval) ((w'.restrict f hw').eval))
    (he' : HEq ((v.restrict f hv).eval) ((v'.restrict f hv').eval)) :
    HEq (((Word.comp w v).restrict f (by simp only [sources, hw, hv, List.nil_append])).eval)
      (((Word.comp w' v').restrict f
        (by simp only [sources, hw', hv', List.nil_append])).eval) := by
  cases ha
  cases hb
  cases hd
  exact heq_of_eq (congrArg₂ ContinuousLinearMap.comp (eq_of_heq he') (eq_of_heq he))

/-- Congruence for the actual restricted residual operations.
Source: polynomial-PEPS 04-compression.tex, lines 246–251 and 351–381. -/
theorem restrict_frame_eval_heq (f : P → Bool) (r : Reg P)
    {a b a' b' : Layout P} (ha : a = a') (hb : b = b')
    (w : Word a b) (v : Word a' b') (hw : w.sources = []) (hv : v.sources = [])
    (he : HEq ((w.restrict f hw).eval) ((v.restrict f hv).eval)) :
    HEq (((Word.frame r w).restrict f hw).eval) (((Word.frame r v).restrict f hv).eval) := by
  cases ha
  cases hb
  by_cases hr : f r.owner = true
  · exact (restrict_frame_true_eval_heq f r w hw hr).trans
      ((heq_of_eq (congrArg (fun A => A.lTensor r.space) (eq_of_heq he))).trans
        (restrict_frame_true_eval_heq f r v hv hr).symm)
  · have hr' := Bool.eq_false_iff.mpr hr
    exact (restrict_frame_false_eval_heq f r w hw hr').trans
      (he.trans (restrict_frame_false_eval_heq f r v hv hr').symm)

/-- Congruence for the actual restricted residual operations.
Source: polynomial-PEPS 04-compression.tex, lines 246–251 and 351–381. -/
theorem restrict_frameList_eval_heq (f : P → Bool)
    {a b a' b' : Layout P} (ha : a = a') (hb : b = b')
    (w : Word a b) (v : Word a' b') (hw : w.sources = []) (hv : v.sources = [])
    (he : HEq ((w.restrict f hw).eval) ((v.restrict f hv).eval))
    (rs rs' : Layout P) (hrs : rs = rs') :
    HEq (((Word.frameList rs w).restrict f ((sources_frameList _ _).trans hw)).eval)
      (((Word.frameList rs' v).restrict f ((sources_frameList _ _).trans hv)).eval) := by
  cases hrs
  induction rs with
  | nil => exact he
  | cons r rs ih =>
      exact restrict_frame_eval_heq f r (congrArg (List.append rs) ha)
        (congrArg (List.append rs) hb) _ _ _ _ ih

/-- Congruence for the actual restricted residual operations.
Source: polynomial-PEPS 04-compression.tex, lines 246–251 and 351–381. -/
theorem restrict_localPart_comp_eval_heq (f : P → Bool) {a b d : Layout P}
    (w w' : Word a b) (v v' : Word b d)
    (hw : w.sources.layout = w'.sources.layout)
    (hv : v.sources.layout = v'.sources.layout)
    (he : HEq ((w.localPart.restrict f w.sources_localPart).eval)
      ((w'.localPart.restrict f w'.sources_localPart).eval))
    (he' : HEq ((v.localPart.restrict f v.sources_localPart).eval)
      ((v'.localPart.restrict f v'.sources_localPart).eval)) :
    HEq ((((Word.comp w v).localPart).restrict f (Word.comp w v).sources_localPart).eval)
      ((((Word.comp w' v').localPart).restrict f (Word.comp w' v').sources_localPart).eval) := by
  have hc : ((Word.frameList v.sources.layout w.localPart).comp v.localPart).sources = [] := by
    simp only [sources, sources_frameList, sources_localPart, List.nil_append]
  have hc' : ((Word.frameList v'.sources.layout w'.localPart).comp v'.localPart).sources = [] := by
    simp only [sources, sources_frameList, sources_localPart, List.nil_append]
  unfold localPart
  refine (restrict_castInput_eval_heq f _ _ hc).trans ?_
  refine HEq.trans ?_ (restrict_castInput_eval_heq f _ _ hc').symm
  apply restrict_comp_eval_heq f
    (congrArg₂ (fun x y => x ++ (y ++ a)) hv hw)
    (congrArg (fun x => x ++ b) hv) rfl
  · exact restrict_frameList_eval_heq f (congrArg (fun x => x ++ a) hw) rfl
      _ _ _ _ he _ _ hv
  · exact he'
/-- Congruence for the actual restricted residual operations.
Source: polynomial-PEPS 04-compression.tex, lines 246–251 and 351–381. -/
theorem restrict_moveHead_eval_heq (f : P → Bool) (r : Reg P)
    (s s' : Layout P) (hs : s = s') (a : Layout P) :
    HEq (((Word.moveHead r s a).restrict f (sources_moveHead _ _ _)).eval)
      (((Word.moveHead r s' a).restrict f (sources_moveHead _ _ _)).eval) := by
  cases hs
  rfl

/-- Congruence for the actual restricted residual operations.
Source: polynomial-PEPS 04-compression.tex, lines 246–251 and 351–381. -/
theorem restrict_localPart_frame_eval_heq (f : P → Bool) (r : Reg P)
    {a b : Layout P} (w v : Word a b) (hs : w.sources.layout = v.sources.layout)
    (he : HEq ((w.localPart.restrict f w.sources_localPart).eval)
      ((v.localPart.restrict f v.sources_localPart).eval)) :
    HEq ((((Word.frame r w).localPart).restrict f (Word.frame r w).sources_localPart).eval)
      ((((Word.frame r v).localPart).restrict f (Word.frame r v).sources_localPart).eval) := by
  unfold localPart
  apply restrict_comp_eval_heq f
    (congrArg (fun s => s ++ r :: a) hs)
    (congrArg (fun s => r :: (s ++ a)) hs) rfl
  · exact restrict_moveHead_eval_heq f r _ _ hs a
  · exact restrict_frame_eval_heq f r (congrArg (fun s => s ++ a) hs) rfl _ _ _ _ he
end Word
end TNLean.PEPS.PairEffect
