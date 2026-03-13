/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.Primitivity.Equivalence
import TNLean.Wielandt.SpanGrowth.NonzeroTraceProduct

/-!
# Lemma 1 — paper-facing nonzero-trace wrapper (arXiv:0909.5347)

This file packages the current formal version of **Lemma 1** from
Sanz–Pérez-García–Wolf–Cirac, *A quantum version of Wielandt's inequality*
(arXiv:0909.5347), and the corresponding discussion in Wolf's Chapter 6, in the
paper-facing `IsPrimitivePaper` language.

## Main result

* `exists_nonzero_trace_word_of_isPrimitivePaper`:
  if `A` is normalized and primitive in the paper's sense, then there exists a
  word product with nonzero trace.

## Quantitative status

The present wrapper is intentionally honest about the available bound: it uses
our completed backend theorem `exists_nonzero_trace_word`, which currently gives

a word of length at most `D^2`.

The sharper paper/Wolf quantitative form
`D^2 - krausRank A + 1` (and, for a minimal Kraus family, `D^2 - d + 1`) is not
formalized yet and remains future work.

## Proof strategy

Use Proposition 3 to pass from `IsPrimitivePaper A` to eventually full Kraus
rank, rewrite this as `IsNormal A`, and then apply the backend nonzero-trace
result.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-- **Lemma 1** (paper-facing wrapper).

If `A` is normalized and primitive in the paper sense, then there exists a
word `w` with `|w| ≤ D^2` such that `tr (evalWord A w) ≠ 0`.

This is the current coarse formal bound coming from
`exists_nonzero_trace_word`. The sharper paper/Wolf bound
`D^2 - krausRank A + 1` is still future work.
Paper: arXiv:0909.5347, Lemma 1; Wolf, Chapter 6.
-/
theorem exists_nonzero_trace_word_of_isPrimitivePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    ∃ w : List (Fin d), w.length ≤ D ^ 2 ∧ Matrix.trace (evalWord A w) ≠ 0 := by
  exact exists_nonzero_trace_word A (isNormal_of_isPrimitivePaper A hNorm hPrim)

end MPSTensor
