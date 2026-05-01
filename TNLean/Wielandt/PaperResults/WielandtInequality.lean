/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.Primitivity.Equivalence
import TNLean.Wielandt.PaperResults.EigenvectorSpreading
import TNLean.Wielandt.PaperResults.MatrixSpanSharpBound
import TNLean.Wielandt.PaperResults.NonzeroTraceWord
import TNLean.Wielandt.SpanGrowth.InvertibleWordSpan
import TNLean.Wielandt.RankOne.Products

/-!
# Theorem 1 — Quantum Wielandt's inequality (arXiv:0909.5347 / Wolf §6.9)

This file contains the public paper-level statements for the currently
formalized parts of **Theorem 1** from Sanz–Pérez-García–Wolf–Cirac,
*A quantum version of Wielandt's inequality* (arXiv:0909.5347), equivalently
Wolf's Theorem 6.9 in *Quantum Channels & Operations: Guided Tour*.

## What is formalized here

### Part 1 — Index bound `q(E_A) ≤ i(A)`

* `qIndex_le_iIndex_of_isPrimitivePaper`: under paper primitivity and
  normalization, the primitivity index `q(E_A)` is at most the full-Kraus-rank
  index `i(A)`. This is equation (2) of arXiv:0909.5347 and appears immediately
  after Proposition 3 in the paper.

### Part 2 — Case (3): noninvertible one-step element with nonzero eigenvalue

Theorem 1 gives the case-(3) bound:
*if the one-step subspace `S₁(A) = wordSpan A 1` contains a noninvertible matrix
with a nonzero eigenvalue, then `i(A) ≤ D²`.*

* `wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_noninvertible_eigenvector`:
  under paper primitivity, normalization, `X ∈ wordSpan A 1`, noninvertibility of
  `X`, and eigenvector data `φ ≠ 0`, `μ ≠ 0`, we prove
  `wordSpan A (D ^ 2) = ⊤`.

* `iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector`:
  the corresponding numeric bound `iIndex A ≤ D ^ 2`.

The former single-Kraus statements
`wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector` and
`iIndex_le_sq_of_noninvertible_eigenvector` are retained as corollaries.

### Part 3 — Case (2): invertible one-step element

Theorem 1 also gives the case-(2) bound:
*if `wordSpan A 1` contains an invertible matrix, then
`i(A) ≤ D² − krausRank(A) + 1`.*

* `wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_isUnit`:
  under paper primitivity, normalization, `X ∈ wordSpan A 1`, and `IsUnit X`, we
  prove `wordSpan A (D ^ 2 - krausRank A + 1) = ⊤`.

* `iIndex_le_of_mem_wordSpan_one_of_isUnit`:
  the corresponding numeric bound
  `iIndex A ≤ D ^ 2 - krausRank A + 1`.

The former single-Kraus statements `wordSpan_eq_top_of_isPrimitivePaper_of_isUnit`
and `iIndex_le_of_isPrimitivePaper_of_isUnit` are retained as corollaries.  The
proofs add the chosen one-step element as a redundant generator and use the
word-span invariance lemmas from `SpanGrowth/InvertibleWordSpan.lean`.

Within TNLean these results are currently standalone paper-level theorem statements:
the canonical / FT / BNT development does not import them directly.

This file is the preferred public entry point for the currently formalized
Theorem 1 statements. The auxiliary module `QuantumWielandt.lean` keeps a
backward-compatible exact-word-span witness theorem with an explicit
aperiodicity argument in its statement; it is not the default paper-level formulation.

### Part 4 — Case (1): general bound

* `iIndex_le_general_of_isPrimitivePaper`:
  the full general bound `i(A) ≤ (D² − krausRank(A) + 1) · D²`.

The proof uses the blocking trick: the sharp Lemma 1 word product of length
`n ≤ D² − krausRank(A) + 1` becomes a Kraus operator of the `n`-blocked tensor.
Writing `B := blockTensor A n`, the blocked invertible case uses case (2) to get
`wordSpan B (D² - krausRank B + 1) = ⊤`, which is then padded to level `D²`.
The blocked noninvertible case uses case (3) to get `wordSpan B (D²) = ⊤`
directly. Transferring the blocked conclusion back to the original tensor
yields the general bound.

The proof handles the edge case where all Kraus operators are nilpotent
(no Kraus operator has a nonzero eigenvalue) by using the positive-length
strengthening of Lemma 1: for `D ≥ 2`, the positive-level cumulative span of
positive-length words reaches `M_D(ℂ)` by the sharp bound, so there is always a
positive-length word with nonzero trace within that range.

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

/-- **Theorem 1, case (3)**: under the paper-faithful one-step subspace
noninvertible eigenvalue hypotheses, `wordSpan A (D ^ 2) = ⊤`.

If `A` is normalized and primitive in the paper's sense, and some arbitrary
matrix `X ∈ S₁(A) = wordSpan A 1` is noninvertible and has a nonzero eigenvalue
with eigenvector `φ ≠ 0`, then the exact word span at level `D ^ 2` is the full
matrix algebra.

The proof adds `X` as a redundant first generator. Since `X ∈ S₁(A)`, this does
not change any exact word span or the Kraus rank; it only lets us reuse the
single-generator backend with `X` as the distinguished first entry.

Paper: arXiv:0909.5347, Theorem 1 case (3); Wolf, Theorem 6.9.
-/
theorem wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_noninvertible_eigenvector
    [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ wordSpan A 1)
    (hNotInv : ¬ IsUnit (toLin' X))
    {φ : Fin D → ℂ} {μ : ℂ} (hφ : φ ≠ 0) (hμ : μ ≠ 0)
    (heig : X *ᵥ φ = μ • φ) :
    wordSpan A (D ^ 2) = ⊤ := by
  let B : MPSTensor (d + 1) D := oneStepAugment A X
  have hN : IsNormal A := isNormal_of_isPrimitivePaper A hNorm hPrim
  have hNB : IsNormal B := by
    simpa [B] using isNormal_oneStepAugment_of_mem_wordSpan_one A hX hN
  have heigB : B (0 : Fin (d + 1)) *ᵥ φ = μ • φ := by
    simpa [B, oneStepAugment] using heig
  have hNotInvB : ¬ IsUnit (toLin' (B (0 : Fin (d + 1)))) := by
    simpa [B, oneStepAugment] using hNotInv
  have hCum : cumulativeVectorSpan B φ (D - 1) = ⊤ :=
    eigenvector_spreading B φ hφ (0 : Fin (d + 1)) μ hμ heigB hNB
  have hVec : vectorSpreadSpan B φ (D - 1) = ⊤ :=
    vectorSpreadSpan_eq_top_of_cumulativeVectorSpan_eq_top_of_eigenvector
      B φ (D - 1) (0 : Fin (d + 1)) μ hμ heigB hCum
  have hRankOne : ∀ ψ : Fin D → ℂ,
      vecMulVec φ ψ ∈ wordSpan B (D ^ 2 - D + 1) :=
    vecMulVec_eigenvector_exact_wordSpan B (0 : Fin (d + 1)) hNB hNotInvB hμ heigB
  have hBasis : ∀ j : Fin D,
      vecMulVec φ (Pi.single j (1 : ℂ)) ∈ wordSpan B (D ^ 2 - D + 1) :=
    fun j => hRankOne (Pi.single j 1)
  have hAssembly : wordSpan B ((D - 1) + (D ^ 2 - D + 1)) = ⊤ :=
    wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis B φ hVec hBasis
  have hD_pos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hArith : (D - 1) + (D ^ 2 - D + 1) = D ^ 2 := by
    have hDD2 : D ≤ D ^ 2 := by
      calc
        D = D * 1 := (Nat.mul_one D).symm
        _ ≤ D * D := Nat.mul_le_mul_left D hD_pos
        _ = D ^ 2 := (sq D).symm
    zify [hD_pos, hDD2]
    ring
  have hBtop : wordSpan B (D ^ 2) = ⊤ := by
    rwa [hArith] at hAssembly
  have hEq : wordSpan B (D ^ 2) = wordSpan A (D ^ 2) := by
    simpa [B] using wordSpan_oneStepAugment_eq A hX (D ^ 2)
  rwa [hEq] at hBtop

/-- **Theorem 1, case (3)**: under the paper-faithful one-step subspace
noninvertible eigenvalue hypotheses, `iIndex A ≤ D ^ 2`.

Paper: arXiv:0909.5347, Theorem 1 case (3); Wolf, Theorem 6.9.
-/
theorem iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector
    [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ wordSpan A 1)
    (hNotInv : ¬ IsUnit (toLin' X))
    {φ : Fin D → ℂ} {μ : ℂ} (hφ : φ ≠ 0) (hμ : μ ≠ 0)
    (heig : X *ᵥ φ = μ • φ) :
    iIndex A ≤ D ^ 2 := by
  have htop : wordSpan A (D ^ 2) = ⊤ :=
    wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_noninvertible_eigenvector
      A hNorm hPrim hX hNotInv hφ hμ heig
  exact Nat.sInf_le (show D ^ 2 ∈ {n : ℕ | wordSpan A n = ⊤} from htop)

/-- **Theorem 1, case (3)**: generator corollary of the one-step subspace theorem.

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
  exact
    wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_noninvertible_eigenvector
      A hNorm hPrim (apply_mem_wordSpan_one A i₀) hNotInv hφ hμ heig

/-- **Theorem 1, case (3)**: generator corollary of the one-step subspace theorem.

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
  exact
    iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector
      A hNorm hPrim (apply_mem_wordSpan_one A i₀) hNotInv hφ hμ heig

/-! ## Part 3: Case (2) — invertible one-step subspace element -/

/-- **Theorem 1, case (2)**: under the paper-faithful one-step subspace
invertibility hypothesis, `wordSpan A (D ^ 2 - krausRank A + 1) = ⊤`.

If `A` is normalized and primitive in the paper's sense and some arbitrary
matrix `X ∈ S₁(A) = wordSpan A 1` is invertible, then the sharp case-(2)
word-length bound holds.

The proof adds `X` as a redundant first generator. This leaves every exact word
span and `krausRank` unchanged, and reduces the statement to the existing
single-generator invertible backend.

Paper: arXiv:0909.5347, Theorem 1 case (2); Wolf, Theorem 6.9.
-/
theorem wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_isUnit
    [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ wordSpan A 1)
    (hInv : IsUnit X) :
    wordSpan A (D ^ 2 - krausRank A + 1) = ⊤ := by
  let B : MPSTensor (d + 1) D := oneStepAugment A X
  have hN : IsNormal A := isNormal_of_isPrimitivePaper A hNorm hPrim
  have hNB : IsNormal B := by
    simpa [B] using isNormal_oneStepAugment_of_mem_wordSpan_one A hX hN
  have hInvB : IsUnit (B (0 : Fin (d + 1))) := by
    simpa [B, oneStepAugment] using hInv
  have hKraus : krausRank B = krausRank A := by
    simpa [B] using krausRank_oneStepAugment A hX
  have hBtop : wordSpan B (D ^ 2 - krausRank B + 1) = ⊤ :=
    wordSpan_eq_top_of_isNormal_of_isUnit B (0 : Fin (d + 1)) hInvB hNB
  have hBtop' : wordSpan B (D ^ 2 - krausRank A + 1) = ⊤ := by
    simpa [hKraus] using hBtop
  have hEq : wordSpan B (D ^ 2 - krausRank A + 1) =
      wordSpan A (D ^ 2 - krausRank A + 1) := by
    simpa [B] using wordSpan_oneStepAugment_eq A hX (D ^ 2 - krausRank A + 1)
  rwa [hEq] at hBtop'

/-- **Theorem 1, case (2)**: under the paper-faithful one-step subspace
invertibility hypothesis, `iIndex A ≤ D ^ 2 - krausRank A + 1`.

Paper: arXiv:0909.5347, Theorem 1 case (2); Wolf, Theorem 6.9.
-/
theorem iIndex_le_of_mem_wordSpan_one_of_isUnit
    [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ wordSpan A 1)
    (hInv : IsUnit X) :
    iIndex A ≤ D ^ 2 - krausRank A + 1 := by
  have htop : wordSpan A (D ^ 2 - krausRank A + 1) = ⊤ :=
    wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_isUnit
      A hNorm hPrim hX hInv
  exact Nat.sInf_le
    (show D ^ 2 - krausRank A + 1 ∈ {n : ℕ | wordSpan A n = ⊤} from htop)

/-- **Theorem 1, case (2)**: generator corollary of the one-step subspace theorem.

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
  exact wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_isUnit
    A hNorm hPrim (apply_mem_wordSpan_one A i₀) hInv

/-- **Theorem 1, case (2)**: generator corollary of the one-step subspace theorem.

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
  exact iIndex_le_of_mem_wordSpan_one_of_isUnit
    A hNorm hPrim (apply_mem_wordSpan_one A i₀) hInv

/-! ## Part 4: Case (1) — General bound via blocking

The full Wielandt bound combines sharp Lemma 1 (a word product of length
≤ D² − krausRank(A) + 1 has nonzero trace) with the blocking trick: the word
product becomes a Kraus operator of the `n`-blocked tensor. In the blocked
invertible case, case (2) gives a sharper level
`D² - krausRank (blockTensor A n) + 1`, which is then padded to `D²`; in the
blocked noninvertible case, case (3) gives `wordSpan (blockTensor A n) (D²) = ⊤`
directly. This transfers to `wordSpan A (D² · n) = ⊤`.

Paper: arXiv:0909.5347, Theorem 1 case (1); Wolf, Theorem 6.9. -/

/-- Auxiliary: for D = 1, `wordSpan A 0 = ⊤`. The span of `{1}` in the
1×1 matrix algebra is the whole space. -/
private theorem wordSpan_zero_eq_top_of_D_eq_one
    (A : MPSTensor d 1) : wordSpan A 0 = ⊤ := by
  rw [eq_top_iff]
  -- Every 1×1 matrix is a scalar multiple of the identity
  intro M _
  have : M = M 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j; fin_cases i; fin_cases j; simp
  rw [this]
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ wordSpan A 0 := by
    have := evalWord_mem_wordSpan A ([] : List (Fin d))
    simpa [evalWord] using this
  exact Submodule.smul_mem _ _ h1

/-- Auxiliary: for D = 1, `iIndex A = 0`. -/
private theorem iIndex_eq_zero_of_D_eq_one
    (A : MPSTensor d 1) : iIndex A = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (wordSpan_zero_eq_top_of_D_eq_one A))

/-- **Theorem 1, case (1)**: the general Wielandt bound
`iIndex A ≤ (D² − krausRank A + 1) · D²`.

Under paper primitivity and normalization:
1. By sharp Lemma 1, there exists a word `w` of length
   `n ≤ D² − krausRank(A) + 1` with `tr(evalWord A w) ≠ 0`.
2. This matrix has a nonzero eigenvalue `μ` with eigenvector `φ`.
3. The `n`-blocked tensor `blockTensor A n` has this matrix as a Kraus operator.
4. In the blocked invertible case, case (2) yields
   `wordSpan (blockTensor A n) (D² - krausRank (blockTensor A n) + 1) = ⊤`,
   hence also `wordSpan (blockTensor A n) (D²) = ⊤`; in the blocked
   noninvertible case, case (3) gives `wordSpan (blockTensor A n) (D²) = ⊤`
   directly.
5. Transferring back: `wordSpan A (D² · n) = ⊤`.
6. Hence `i(A) ≤ D² · n ≤ (D² − krausRank(A) + 1) · D²`.

Paper: arXiv:0909.5347, Theorem 1; Wolf, Theorem 6.9.
-/
theorem iIndex_le_general_of_isPrimitivePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    iIndex A ≤ (D ^ 2 - krausRank A + 1) * D ^ 2 := by
  have hN : IsNormal A := isNormal_of_isPrimitivePaper A hNorm hPrim
  have hD_pos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  -- Case 1: D = 1 — trivial since iIndex = 0
  by_cases hD1 : D = 1
  · subst hD1; simp [iIndex_eq_zero_of_D_eq_one]
  · -- Case 2: D ≥ 2 — use positive-length trace word + blocking argument
    have hD2 : 2 ≤ D := by omega
    -- Get a **positive-length** sharp nonzero-trace word
    have hexists := exists_nonzero_trace_word_of_isPrimitivePaper_sharp_pos hD2 A hNorm hPrim
    obtain ⟨w, hw_pos, hw_len, hw_tr⟩ := hexists
    -- Extract eigenvalue and eigenvector from this word
    obtain ⟨μ, φ, hμ, hφ, heig⟩ := exists_eigenvector_of_trace_ne_zero _ hw_tr
    set n := w.length with hn_def
    have hn_pos : 0 < n := hw_pos
    -- Set up the blocked tensor
    set B := blockTensor (d := d) (D := D) A n
    -- B is IsNormal
    have hNB : IsNormal B := isNormal_blockTensor A n hn_pos hN
    -- B is normalized
    have hNormB : ∑ i, (B i)ᴴ * B i = 1 := leftCanonical_blockTensor A n hNorm
    -- B is IsPrimitivePaper (from IsNormal, no normalization needed)
    have hPrimB : IsPrimitivePaper B := isPrimitivePaper_of_isNormal B hNB
    -- Encode w as a blocked index
    set σ₀ : Fin n → Fin d := w.get with hσ₀_def
    set i₀ := encodeBlock d n σ₀ with hi₀_def
    -- The Kraus operator B i₀ = evalWord A w
    have hBi₀ : B i₀ = evalWord A w := by
      have h1 : B i₀ = evalWord A (List.ofFn σ₀) :=
        blockTensor_apply_encodeBlock A n σ₀
      have h2 : List.ofFn σ₀ = w := by simp [σ₀, List.ofFn_get]
      rw [h1, h2]
    -- The eigenvector equation transfers to B i₀
    have heigB : B i₀ *ᵥ φ = μ • φ := by rw [hBi₀]; exact heig
    -- Case split on invertibility
    by_cases hInv : IsUnit (B i₀)
    · -- B i₀ is invertible: apply case (2) to blocked tensor, then permanence
      have hInvTop := wordSpan_eq_top_of_isNormal_of_isUnit B i₀ hInv hNB
      -- Use permanence to extend to level D² (since D²-krausRank B+1 ≤ D²)
      have hD2top : wordSpan B (D ^ 2) = ⊤ := by
        apply wordSpan_eq_top_of_ge_of_isUnit B i₀ hInv hInvTop
        have hkB : krausRank B ≤ D ^ 2 := by
          simpa [krausRank] using wordSpan_finrank_le B 1
        -- krausRank B ≥ 1 since B i₀ is a unit (hence nonzero) in wordSpan B 1
        have hkB_pos : 1 ≤ krausRank B := by
          rw [krausRank, Nat.one_le_iff_ne_zero]
          intro h0
          have hbot := Submodule.finrank_eq_zero.mp h0
          have hBmem : B i₀ ∈ wordSpan B 1 := by
            have := evalWord_mem_wordSpan B ([i₀] : List (Fin (blockPhysDim d n)))
            simpa [evalWord] using this
          rw [hbot] at hBmem
          change B i₀ = 0 at hBmem
          exact not_isUnit_zero (hBmem ▸ hInv)
        omega
      -- Transfer: wordSpan A (D² * n) = ⊤
      have hAtop : wordSpan A (D ^ 2 * n) = ⊤ :=
        wordSpan_eq_top_of_blockTensor_wordSpan_eq_top A n (D ^ 2) hD2top
      -- iIndex A ≤ D² * n ≤ D² * (D²-d'+1) = (D²-d'+1) * D²
      calc iIndex A ≤ D ^ 2 * n := Nat.sInf_le hAtop
        _ ≤ D ^ 2 * (D ^ 2 - krausRank A + 1) := by
            apply Nat.mul_le_mul_left; exact hw_len
        _ = (D ^ 2 - krausRank A + 1) * D ^ 2 := Nat.mul_comm _ _
    · -- B i₀ is not invertible: apply case (3) to blocked tensor
      have hNotInv : ¬ IsUnit (toLin' (B i₀)) :=
        fun h => hInv (Matrix.isUnit_toLin'_iff.mp h)
      have hD2top : wordSpan B (D ^ 2) = ⊤ :=
        wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector
          B hNormB hPrimB i₀ hNotInv hφ hμ heigB
      -- Transfer: wordSpan A (D² * n) = ⊤
      have hAtop : wordSpan A (D ^ 2 * n) = ⊤ :=
        wordSpan_eq_top_of_blockTensor_wordSpan_eq_top A n (D ^ 2) hD2top
      calc iIndex A ≤ D ^ 2 * n := Nat.sInf_le hAtop
        _ ≤ D ^ 2 * (D ^ 2 - krausRank A + 1) := by
            apply Nat.mul_le_mul_left; exact hw_len
        _ = (D ^ 2 - krausRank A + 1) * D ^ 2 := Nat.mul_comm _ _

end MPSTensor
