/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.Primitivity.Equivalence
import TNLean.Wielandt.PaperResults.EigenvectorSpreading
import TNLean.Wielandt.PaperResults.MatrixSpanSharpBound
import TNLean.Wielandt.SpanGrowth.InvertibleWordSpan

/-!
# Theorem 1 — Quantum Wielandt's inequality (arXiv:0909.5347 / Wolf §6.9)

This file packages the public paper-facing wrappers for the currently
formalized parts of **Theorem 1** from Sanz–Pérez-García–Wolf–Cirac,
*A quantum version of Wielandt's inequality* (arXiv:0909.5347), equivalently
Wolf's Theorem 6.9 in *Quantum Channels & Operations: Guided Tour*.

## What is formalized here

### Part 1 — Index bound `q(E_A) ≤ i(A)`

* `qIndex_le_iIndex_of_isPrimitivePaper`: under paper primitivity and
  normalization, the primitivity index `q(E_A)` is at most the full-Kraus-rank
  index `i(A)`. This is equation (2) of arXiv:0909.5347 and appears immediately
  after Proposition 3 in the paper.

### Part 2 — Case (3): noninvertible Kraus operator with nonzero eigenvalue

Theorem 1 gives the case-(3) bound:
*if some Kraus operator `A_{i₀}` is noninvertible and has a nonzero eigenvalue,
then `i(A) ≤ D²`.*

* `wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector`:
  under paper primitivity, normalization, and the case-(3) hypotheses
  (`A i₀` noninvertible, eigenvector `φ ≠ 0` with `μ ≠ 0`), we prove
  `wordSpan A (D ^ 2) = ⊤`.

* `iIndex_le_sq_of_noninvertible_eigenvector`:
  the corresponding numeric bound `iIndex A ≤ D ^ 2`.

### Part 3 — Case (2): invertible Kraus operator

Theorem 1 also gives the case-(2) bound:
*if some Kraus operator `A_{i₀}` is invertible, then
`i(A) ≤ D² − krausRank(A) + 1`.*

* `wordSpan_eq_top_of_isPrimitivePaper_of_isUnit`:
  under paper primitivity, normalization, and `IsUnit (A i₀)`, we prove
  `wordSpan A (D ^ 2 - krausRank A + 1) = ⊤`.

* `iIndex_le_of_isPrimitivePaper_of_isUnit`:
  the corresponding numeric bound
  `iIndex A ≤ D ^ 2 - krausRank A + 1`.

These case-(2) wrappers pass from paper primitivity to `IsNormal A` and then
invoke the backend theorem `wordSpan_eq_top_of_isNormal_of_isUnit` from
`SpanGrowth/InvertibleWordSpan.lean`.

Within TNLean these results are currently standalone paper-facing endpoints:
the canonical / FT / BNT assembly does not import them directly.

This file is the preferred public entry point for the currently formalized
Theorem 1 wrappers. The auxiliary module `QuantumWielandt.lean` packages a
conditional aperiodicity-based route and is not the default paper-facing API.

## What remains as future work

* **Case (1)** / full general bound:
  `i(A) ≤ (D² − krausRank(A) + 1) · D²`, which combines cases (2) and (3).

Note: **Sharp Lemma 1** using `krausRank A` is now available in
`NonzeroTraceWord.lean` as `exists_nonzero_trace_word_of_isPrimitivePaper_sharp`.

## References

* [SPGWC09] Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347, Theorem 1
* [Wolf12] Wolf, *Quantum Channels & Operations*, Theorem 6.9
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-! ## Part 1: q(E_A) ≤ i(A) -/

/-- **Theorem 1 / equation (2)**: under paper primitivity and normalization,
the primitivity index is at most the full-Kraus-rank index.

Paper: arXiv:0909.5347, equation (2) after Proposition 3; Wolf, Theorem 6.9.
-/
theorem qIndex_le_iIndex_of_isPrimitivePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    qIndex A ≤ iIndex A := by
  exact prop3_qIndex_le_iIndex A
    (hasEventuallyFullKrausRank_of_isPrimitivePaper A hNorm hPrim)

/-! ## Part 2: Case (3) — noninvertible with nonzero eigenvalue gives `D²` -/

/-- **Theorem 1, case (3)**: under the noninvertible eigenvalue hypotheses,
`wordSpan A (D ^ 2) = ⊤`.

If `A` is normalized and primitive in the paper's sense, `A i₀` is not
invertible, and `φ ≠ 0` is an eigenvector of `A i₀` with eigenvalue `μ ≠ 0`,
then the exact word span at level `D ^ 2` is the full matrix algebra.

Paper: arXiv:0909.5347, Theorem 1 case (3); Wolf, Theorem 6.9.
-/
theorem wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector
    [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A)
    (i₀ : Fin d)
    (hNotInv : ¬ IsUnit (toLin' (A i₀)))
    {φ : Fin D → ℂ} {μ : ℂ} (hφ : φ ≠ 0) (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    wordSpan A (D ^ 2) = ⊤ := by
  have hVec : vectorSpreadSpan A φ (D - 1) = ⊤ :=
    vectorSpreadSpan_eq_top_of_isPrimitivePaper_of_eigenvector
      A hNorm hPrim φ hφ i₀ μ hμ heig
  have hRankOne : ∀ ψ : Fin D → ℂ, vecMulVec φ ψ ∈ wordSpan A (D ^ 2 - D + 1) :=
    vecMulVec_mem_wordSpan_of_isPrimitivePaper_of_noninvertible_eigenvector
      A hNorm hPrim i₀ hNotInv hμ heig
  have hBasis : ∀ j : Fin D,
      vecMulVec φ (Pi.single j (1 : ℂ)) ∈ wordSpan A (D ^ 2 - D + 1) :=
    fun j => hRankOne (Pi.single j 1)
  have hAssembly : wordSpan A ((D - 1) + (D ^ 2 - D + 1)) = ⊤ :=
    wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis A φ hVec hBasis
  have hD_pos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hArith : (D - 1) + (D ^ 2 - D + 1) = D ^ 2 := by
    have hDD2 : D ≤ D ^ 2 := by
      calc
        D = D * 1 := (Nat.mul_one D).symm
        _ ≤ D * D := Nat.mul_le_mul_left D hD_pos
        _ = D ^ 2 := (sq D).symm
    zify [hD_pos, hDD2]
    ring
  rwa [hArith] at hAssembly

/-- **Theorem 1, case (3)**: under the noninvertible eigenvalue hypotheses,
`iIndex A ≤ D ^ 2`.

Paper: arXiv:0909.5347, Theorem 1 case (3); Wolf, Theorem 6.9.
-/
theorem iIndex_le_sq_of_noninvertible_eigenvector
    [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A)
    (i₀ : Fin d)
    (hNotInv : ¬ IsUnit (toLin' (A i₀)))
    {φ : Fin D → ℂ} {μ : ℂ} (hφ : φ ≠ 0) (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    iIndex A ≤ D ^ 2 := by
  have htop : wordSpan A (D ^ 2) = ⊤ :=
    wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector
      A hNorm hPrim i₀ hNotInv hφ hμ heig
  exact Nat.sInf_le (show D ^ 2 ∈ {n : ℕ | wordSpan A n = ⊤} from htop)

/-! ## Part 3: Case (2) — invertible Kraus operator -/

/-- **Theorem 1, case (2)**: under an invertible Kraus operator hypothesis,
`wordSpan A (D ^ 2 - krausRank A + 1) = ⊤`.

If `A` is normalized and primitive in the paper's sense and some Kraus operator
`A i₀` is invertible, then the sharp case-(2) word-length bound holds.

Paper: arXiv:0909.5347, Theorem 1 case (2); Wolf, Theorem 6.9.
-/
theorem wordSpan_eq_top_of_isPrimitivePaper_of_isUnit
    [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A)
    (i₀ : Fin d)
    (hInv : IsUnit (A i₀)) :
    wordSpan A (D ^ 2 - krausRank A + 1) = ⊤ := by
  exact wordSpan_eq_top_of_isNormal_of_isUnit A i₀ hInv
    (isNormal_of_isPrimitivePaper A hNorm hPrim)

/-- **Theorem 1, case (2)**: under an invertible Kraus operator hypothesis,
`iIndex A ≤ D ^ 2 - krausRank A + 1`.

Paper: arXiv:0909.5347, Theorem 1 case (2); Wolf, Theorem 6.9.
-/
theorem iIndex_le_of_isPrimitivePaper_of_isUnit
    [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A)
    (i₀ : Fin d)
    (hInv : IsUnit (A i₀)) :
    iIndex A ≤ D ^ 2 - krausRank A + 1 := by
  have htop : wordSpan A (D ^ 2 - krausRank A + 1) = ⊤ :=
    wordSpan_eq_top_of_isPrimitivePaper_of_isUnit A hNorm hPrim i₀ hInv
  exact Nat.sInf_le
    (show D ^ 2 - krausRank A + 1 ∈ {n : ℕ | wordSpan A n = ⊤} from htop)

end MPSTensor
