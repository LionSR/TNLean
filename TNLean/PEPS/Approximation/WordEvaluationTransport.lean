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

end TNLean.PEPS.PairEffect.Word
