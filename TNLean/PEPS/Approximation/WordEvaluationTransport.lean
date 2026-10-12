/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordRestriction

/-!
# Evaluation after identifying register lists

The evaluation of an actual word is compatible with the canonical identification
of equal input and output lists. This shared result is used by source-slot maps,
selective preparation, source-position permutations, and effect replacement.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–251 and 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.PairEffect.Word

/-- Evaluation under equal register lists preserves heterogeneous input equality. -/
theorem eval_castLayouts_apply_heq {P : Type} {a b a' b' : Layout P}
    (w : Word a b) (hi : a = a') (ho : b = b')
    {x : Mem a'} {y : Mem a} (hxy : HEq x y) :
    HEq ((w.castLayouts hi ho).eval x) (w.eval y) := by
  cases hi
  cases ho
  exact heq_of_eq (congrArg w.eval (eq_of_heq hxy))

/-- Heterogeneously equal word operators remain equal under composition after
identifying their input, intermediate and output register lists. -/
theorem eval_comp_heq {P : Type} {a b c a' b' c' : Layout P}
    (u : Word a b) (v : Word b c) (u' : Word a' b') (v' : Word b' c')
    (ha : a = a') (hb : b = b') (hc : c = c')
    (hu : HEq u.eval u'.eval) (hv : HEq v.eval v'.eval) :
    HEq (u.comp v).eval (u'.comp v').eval := by
  cases ha
  cases hb
  cases hc
  exact heq_of_eq (congrArg₂ ContinuousLinearMap.comp (eq_of_heq hv) (eq_of_heq hu))

/-- Heterogeneously equal word operators remain equal when framed by the same
register, after identifying their input and output register lists. -/
theorem eval_frame_heq {P : Type} (r : Reg P) {a b a' b' : Layout P}
    (u : Word a b) (v : Word a' b') (ha : a = a') (hb : b = b')
    (hu : HEq u.eval v.eval) : HEq (Word.frame r u).eval (Word.frame r v).eval := by
  cases ha
  cases hb
  exact heq_of_eq (congrArg (fun A : Mem a →L[ℂ] Mem b ↦ A.lTensor r.space)
    (eq_of_heq hu))

/-- Equal register lists give heterogeneously equal identity operators. -/
theorem eval_id_heq {P : Type} {a b : Layout P} (h : a = b) :
    HEq (Word.id a).eval (Word.id b).eval := by
  cases h
  rfl

/-- Restriction preserves the operator after an identification of the input list.
The source inventory is empty; the selected memories are arbitrary. -/
theorem restrict_castInput_eval_heq {P : Type} (f : P → Bool) {a b a' : Layout P}
    (w : Word a b) (h : a = a') (hs : w.sources = []) :
    HEq ((w.castInput h).restrict f ((sources_castInput w h).trans hs)).eval
      (w.restrict f hs).eval := by
  cases h
  rfl

end TNLean.PEPS.PairEffect.Word
