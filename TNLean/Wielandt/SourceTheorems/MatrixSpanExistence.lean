/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.Primitivity.Equivalence
import TNLean.Wielandt.RankOne.ExtractionFull

/-!
# Lemma 2(b) — coarse existential statement (arXiv:0909.5347)

This file states a **coarse existential** version of **Lemma 2(b)** from
Sanz–Pérez-García–Wolf–Cirac, *A quantum version of Wielandt's inequality*
(arXiv:0909.5347), in the `IsPrimitivePaper` language of the paper.

## Main results

* `exists_wordSpan_eq_top_of_isPrimitivePaper`: if `A` is normalized and
  primitive in the paper's sense, then there exists `N` such that the
  `N`-th word span `S_N(A)` is the full matrix algebra `M_D(ℂ)`.

* `forall_vecMulVec_mem_wordSpan_of_isPrimitivePaper`: for any vectors
  `φ ψ : Fin D → ℂ`, the rank-one matrix `|φ⟩⟨ψ|` belongs to `S_N(A)` for the
  same witness `N`.

## Quantitative status

These statements are intentionally **coarse existential** statements. They use the
underlying theorem `wielandt_lemma2b`, which produces a witness `N` without
claiming the paper's exact bound.

They state only the qualitative conclusion `∃ N, S_N(A) = M_D(ℂ)`. In
particular, they do **not** track the explicit `D²` blocked noninvertible bound
or the sharp `D² − D + 1` fixed-length bound. Those quantitative statements are
formalized separately in `SourceTheorems/MatrixSpanSharpBound.lean` and in the
case analysis of `SourceTheorems/WielandtInequality.lean`.

## Proof strategy

1. Use Proposition 3 to pass from `IsPrimitivePaper A` to eventually full Kraus
   rank (`HasEventuallyFullKrausRank A`).
2. Rewrite as `IsNormal A`.
3. Apply the existential theorem `wielandt_lemma2b`.

These statements record Lemma 2(b) of arXiv:0909.5347 / Wolf Section 6.9
in the notation of the source; the FT/BNT formalization does not use them.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-- **Lemma 2(b)** (coarse existential statement).

If `A` is normalized and primitive under the source theorem hypotheses, then there exists `N`
such that `S_N(A) = M_D(ℂ)`.

This is the coarse existential consequence of Lemma 2(b): it does *not* claim
that one may take `N = D² − D + 1`.
Paper: arXiv:0909.5347, Lemma 2(b); Wolf, Chapter 6.
-/
theorem exists_wordSpan_eq_top_of_isPrimitivePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    ∃ N : ℕ, wordSpan A N = ⊤ := by
  exact wielandt_lemma2b A (isNormal_of_isPrimitivePaper A hNorm hPrim)

/-- **Lemma 2(b)** (coarse rank-one corollary).

If `A` is normalized and primitive under the source theorem hypotheses, then there exists `N`
such that every rank-one matrix `|φ⟩⟨ψ|` belongs to `S_N(A)`.

This states the same existential consequence of Lemma 2(b) as
`exists_wordSpan_eq_top_of_isPrimitivePaper`, but stated for rank-one matrices.
Paper: arXiv:0909.5347, Lemma 2(b); Wolf, Chapter 6.
-/
theorem forall_vecMulVec_mem_wordSpan_of_isPrimitivePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    ∃ N : ℕ, ∀ φ ψ : Fin D → ℂ, vecMulVec φ ψ ∈ wordSpan A N := by
  obtain ⟨N, hN⟩ := exists_wordSpan_eq_top_of_isPrimitivePaper A hNorm hPrim
  exact ⟨N, fun φ ψ => hN ▸ Submodule.mem_top⟩

end MPSTensor
