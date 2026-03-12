/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.Prop3
import TNLean.Wielandt.Lemma2
import TNLean.Wielandt.Lemma2bExact

/-!
# Theorem 1 — Quantum Wielandt's inequality (arXiv:0909.5347 / Wolf §6.9)

This file packages the first **public paper-facing results** for **Theorem 1**
(the Quantum Wielandt inequality) from Sanz–Pérez-García–Wolf–Cirac,
*A quantum version of Wielandt's inequality* (arXiv:0909.5347), equivalently
Wolf's Theorem 6.9 in *Quantum Channels & Operations: Guided Tour*.

## What is formalized here

### Part 1 — Index bound `q(E_A) ≤ i(A)`

* `qIndex_le_iIndex_of_isPrimitivePaper`: under paper primitivity and
  normalization, the primitivity index `q(E_A)` is at most the full-Kraus-rank
  index `i(A)`.  This is equation (2) of arXiv:0909.5347 and appears
  immediately after Proposition 3 in the paper.

### Part 2 — Case (3): noninvertible Kraus operator with nonzero eigenvalue

The paper's Theorem 1 gives three cases for bounding `i(A)`. Case (3) states:
*if some Kraus operator `A_{i₀}` is noninvertible and has a nonzero eigenvalue,
then `i(A) ≤ D²`.*

* `wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector`:
  under paper primitivity, normalization, and the case-(3) hypotheses
  (`A i₀` noninvertible, eigenvector `φ ≠ 0` with `μ ≠ 0`), we prove
  `wordSpan A (D ^ 2) = ⊤`.

* `iIndex_le_sq_of_noninvertible_eigenvector`:
  the corresponding numeric bound `iIndex A ≤ D ^ 2`.

## Partial progress toward case (2)

`InvertibleWordSpanGrowth.lean` provides sorry-free infrastructure for
the invertible-element case:

* `wordSpan_finrank_mono_of_isUnit`: `dim(S_{n+1}) ≥ dim(S_n)` when `A i₀`
  is invertible.
* `wordSpan_eq_top_of_ge_of_isUnit`: **permanence** — once `S_N = ⊤`,
  `S_m = ⊤` for all `m ≥ N` under invertibility.

## What remains as future work

* **Case (2) sharp bound**: `i(A) ≤ D² − krausRank(A) + 1` when some
  Kraus operator is invertible. This requires the **strict growth** claim:
  if `dim(S_n) < D²` then `dim(S_{n+1}) > dim(S_n)`. The infrastructure
  (monotonicity, permanence) is in place; the gap is the formal proof
  that dimensional stabilization below `D²` contradicts `IsNormal`,
  following PVWC07 Appendix A.

* **Case (1)** / full general bound: `i(A) ≤ (D² − krausRank(A) + 1) · D²`,
  which combines cases (2) and (3).  Blocked by case (2) sharp bound.

* **Sharp Lemma 1** using `krausRank A` rather than the raw parameter `d`.

## Proof strategy

### q ≤ i

The proof chains:
1. `IsPrimitivePaper → HasEventuallyFullKrausRank` (Proposition 3)
2. `HasEventuallyFullKrausRank → qIndex A ≤ iIndex A` (PrimitiveEquiv)

### Case (3)

The proof combines **Lemma 2(a)** and **Lemma 2(b)**:
1. `IsPrimitivePaper → IsNormal A` (Proposition 3 bridge)
2. **Lemma 2(a)**: `vectorSpreadSpan A φ (D − 1) = ⊤`
   (eigenvector spreading under normality)
3. **Lemma 2(b)**: `∀ ψ, vecMulVec φ ψ ∈ wordSpan A (D² − D + 1)`
   (exact rank-one placement under noninvertibility + nonzero eigenvalue)
4. **Assembly**: `wordSpan A ((D−1) + (D²−D+1)) = ⊤`
   (from `wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis`)
5. **Arithmetic**: `(D − 1) + (D² − D + 1) = D²`

## References

* [SPGWC09] Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347, Theorem 1
* [Wolf12] Wolf, *Quantum Channels & Operations*, Theorem 6.9
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-! ## Part 1: q(E_A) ≤ i(A) -/

/-- **Theorem 1, index bound `q(E_A) ≤ i(A)`** (arXiv:0909.5347, eq. (2)).

Under paper primitivity and normalization `∑ Aᵢ† Aᵢ = 1`, the primitivity
index `q(E_A)` is at most the full-Kraus-rank index `i(A)`.

This is the first quantitative statement in Theorem 1 of the paper, and appears
as equation (2) immediately after Proposition 3.

**Proof.** Paper primitivity implies eventually full Kraus rank by
Proposition 3.  The bound `qIndex ≤ iIndex` then follows from
`vectorSpreadSpan_eq_top_of_wordSpan_eq_top`: if `wordSpan A (iIndex A) = ⊤`,
then `vectorSpreadSpan A φ (iIndex A) = ⊤` for all nonzero `φ`, so
`qIndex A ≤ iIndex A`. -/
theorem qIndex_le_iIndex_of_isPrimitivePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    qIndex A ≤ iIndex A := by
  have hEventually : HasEventuallyFullKrausRank A :=
    (primitivePaper_iff_hasEventuallyFullKrausRank A hNorm).mp hPrim
  exact qIndex_le_iIndex A hEventually

/-! ## Part 2: Case (3) — noninvertible with nonzero eigenvalue gives `D²` -/

/-- **Theorem 1, case (3): `wordSpan A (D²) = ⊤`** under noninvertible eigenvalue
hypotheses (arXiv:0909.5347 / Wolf 6.9).

If `A` is normalized and primitive in the paper's sense, `A i₀` is **not**
invertible, and `φ ≠ 0` is an eigenvector of `A i₀` with eigenvalue `μ ≠ 0`,
then `wordSpan A (D ^ 2) = ⊤`.

**Proof.** Combines Lemma 2(a) and Lemma 2(b):
- **Lemma 2(a)** gives `vectorSpreadSpan A φ (D − 1) = ⊤`.
- **Lemma 2(b)** gives `∀ ψ, vecMulVec φ ψ ∈ wordSpan A (D² − D + 1)`.
- The **assembly** theorem `wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis`
  yields `wordSpan A ((D−1) + (D²−D+1)) = ⊤`.
- Arithmetic: `(D − 1) + (D² − D + 1) = D²`. -/
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
  -- Lemma 2(a): vectorSpreadSpan A φ (D - 1) = ⊤
  have hVec : vectorSpreadSpan A φ (D - 1) = ⊤ :=
    vectorSpreadSpan_eq_top_of_isPrimitivePaper_of_eigenvector A hNorm hPrim φ hφ i₀ μ hμ heig
  -- Lemma 2(b): ∀ ψ, vecMulVec φ ψ ∈ wordSpan A (D² - D + 1)
  have hRankOne : ∀ ψ : Fin D → ℂ, vecMulVec φ ψ ∈ wordSpan A (D ^ 2 - D + 1) :=
    vecMulVec_mem_wordSpan_of_isPrimitivePaper_of_noninvertible_eigenvector
      A hNorm hPrim i₀ hNotInv hμ heig
  -- In particular, each basis rank-one element
  have hBasis : ∀ j : Fin D,
      vecMulVec φ (Pi.single j (1 : ℂ)) ∈ wordSpan A (D ^ 2 - D + 1) :=
    fun j => hRankOne (Pi.single j 1)
  -- Assembly: wordSpan A ((D - 1) + (D² - D + 1)) = ⊤
  have hAssembly : wordSpan A ((D - 1) + (D ^ 2 - D + 1)) = ⊤ :=
    wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis A φ hVec hBasis
  -- Arithmetic: (D - 1) + (D² - D + 1) = D²
  have hD_pos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hArith : (D - 1) + (D ^ 2 - D + 1) = D ^ 2 := by
    -- D ≤ D² since D = D * 1 ≤ D * D = D²
    have hDD2 : D ≤ D ^ 2 := by
      calc D = D * 1 := (Nat.mul_one D).symm
        _ ≤ D * D := Nat.mul_le_mul_left D hD_pos
        _ = D ^ 2 := (sq D).symm
    zify [hD_pos, hDD2]
    ring
  rwa [hArith] at hAssembly

/-- **Theorem 1, case (3): `iIndex A ≤ D²`** under noninvertible eigenvalue
hypotheses (arXiv:0909.5347 / Wolf 6.9).

If `A` is normalized and primitive in the paper's sense, `A i₀` is **not**
invertible, and `φ ≠ 0` is an eigenvector of `A i₀` with eigenvalue `μ ≠ 0`,
then the full-Kraus-rank index satisfies `iIndex A ≤ D ^ 2`.

This is the numeric form of `wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector`. -/
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

end MPSTensor
