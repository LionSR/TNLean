/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyWord

/-! # Comparison of chronological word evaluations

Two words may record different owners and register lists. Their evaluations
can be compared while retaining these input and output spaces. On fixed
input and output layouts, the comparison gives ordinary operator equality.
It imposes no allowedness or source-free condition and does not assert that
restriction preserves an arbitrary equality of complete operators.

## References

* Polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
  351–434 and 565–588; revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.PairEffect.Word

/-- Compare the evaluations of two words with their actual input and output
spaces. This comparison does not impose allowedness or source-free conditions.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
351–434 and 565–588. -/
def IsEvalComparison {Q R : Type} {a b : Layout Q} {c d : Layout R}
    (u : Word a b) (v : Word c d) : Prop := HEq u.eval v.eval

/-- On fixed input and output layouts, evaluation comparison gives ordinary
operator equality. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 253–267 and 565–588. -/
theorem IsEvalComparison.eval_eq {Q : Type} {a b : Layout Q}
    {u v : Word a b} (h : IsEvalComparison u v) : u.eval = v.eval :=
  eq_of_heq h

end TNLean.PEPS.PairEffect.Word
