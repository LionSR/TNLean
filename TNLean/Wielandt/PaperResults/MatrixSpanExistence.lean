/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.Primitivity.Equivalence
import TNLean.Wielandt.RankOne.ExtractionFull

/-!
# Lemma 2(b) — coarse existential wrapper (arXiv:0909.5347)

This file packages a **coarse existential** version of **Lemma 2(b)** from
Sanz–Pérez-García–Wolf–Cirac, *A quantum version of Wielandt's inequality*
(arXiv:0909.5347), in the paper-facing `IsPrimitivePaper` language.

## Main results

* `exists_wordSpan_eq_top_of_isPrimitivePaper`: if `A` is normalized and
  primitive in the paper's sense, then there exists `N` such that the
  `N`-th word span `S_N(A)` is the full matrix algebra `M_D(ℂ)`.

* `forall_vecMulVec_mem_wordSpan_of_isPrimitivePaper`: for any vectors
  `φ ψ : Fin D → ℂ`, the rank-one matrix `|φ⟩⟨ψ|` belongs to `S_N(A)` for the
  same witness `N`.

## Quantitative status

These wrappers are intentionally **coarse existential** statements. They use the
backend theorem `wielandt_lemma2b`, which produces a sorry-free witness `N`
without claiming the paper's exact bound.

The exact paper-level statement with bound `N = D² − D + 1` is now formalized in
`Lemma2bExact.lean`, but it requires the additional hypothesis that a chosen
Kraus operator `A i₀` is noninvertible and has a nonzero eigenvector. This file
keeps the weaker existential consequence that follows from paper primitivity
alone.

## Proof strategy

1. Use Proposition 3 to pass from `IsPrimitivePaper A` to eventually full Kraus
   rank (`HasEventuallyFullKrausRank A`).
2. Rewrite as `IsNormal A`.
3. Apply the backend existential theorem `wielandt_lemma2b`.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-- **Lemma 2(b)** (coarse existential wrapper).

If `A` is normalized and primitive in the paper sense, then there exists `N`
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

If `A` is normalized and primitive in the paper sense, then there exists `N`
such that every rank-one matrix `|φ⟩⟨ψ|` belongs to `S_N(A)`.

This packages the same existential consequence of Lemma 2(b) as
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
