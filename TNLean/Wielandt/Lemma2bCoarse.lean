/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.Prop3
import TNLean.Wielandt.RankOneExtractionFull

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

These are intentionally honest **coarse existential** wrappers. The backend
theorem `wielandt_lemma2b` currently gives a sorry-free witness `N` whose value
depends on blocking parameters and is not the sharp paper/Wolf bound.

The exact quantitative statement from the paper is that one can take
`N = D² − D + 1` (under additional hypotheses on the Kraus operator chosen for
the eigenvector). That precise bound is **not** formalized yet and remains
future work requiring the one-sided `rectSpan` growth infrastructure.

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

/-- **Lemma 2(b) (coarse existential)**: if `A` is normalized and primitive in
the paper sense, then there exists `N` such that `S_N(A) = M_D(ℂ)`.

This is the coarse existential form — it does *not* claim the exact
paper/Wolf bound `N = D² − D + 1`, only the existence of some `N`.
See the module docstring for quantitative status. -/
theorem exists_wordSpan_eq_top_of_isPrimitivePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    ∃ N : ℕ, wordSpan A N = ⊤ := by
  have hEventually : HasEventuallyFullKrausRank A :=
    (primitivePaper_iff_hasEventuallyFullKrausRank A hNorm).mp hPrim
  have hNormal : IsNormal A :=
    (hasEventuallyFullKrausRank_iff_isNormal A).mp hEventually
  exact wielandt_lemma2b A hNormal

/-- **Lemma 2(b) corollary — rank-one membership**: if `A` is normalized and
primitive in the paper sense, then there exists `N` such that every rank-one
matrix `|φ⟩⟨ψ|` belongs to `S_N(A)`.

This is an immediate consequence of `exists_wordSpan_eq_top_of_isPrimitivePaper`:
when the word span is the full matrix algebra, every matrix is a member. -/
theorem forall_vecMulVec_mem_wordSpan_of_isPrimitivePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    ∃ N : ℕ, ∀ φ ψ : Fin D → ℂ, vecMulVec φ ψ ∈ wordSpan A N := by
  obtain ⟨N, hN⟩ := exists_wordSpan_eq_top_of_isPrimitivePaper A hNorm hPrim
  exact ⟨N, fun φ ψ => hN ▸ Submodule.mem_top⟩

end MPSTensor
