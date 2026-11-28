/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Transfer.Primitivity.Equivalence
import TNLean.MPS.Transfer.Primitivity.RectangularSpan
import TNLean.MPS.Transfer.Primitivity.InvertibleWordSpan
import QICLean.Kraus.Wielandt.RankOne.BoundedWord
import QICLean.Kraus.Wielandt.Inequality.EigenvectorSpreading
import TNLean.MPS.Tensor
import TNLean.MPS.Tensor.Words.WordSpan

/-!
# Theorem 1 — Quantum Wielandt's inequality (arXiv:0909.5347 / Wolf Section 6.9)

This file contains the stated index bounds in **Theorem 1** of
Sanz–Pérez-García–Wolf–Cirac,
*A quantum version of Wielandt's inequality* (arXiv:0909.5347), equivalently
Wolf's Theorem 6.9 in *Quantum Channels & Operations: Guided Tour*.

## What is formalized here

The source states its theorem for a primitive channel `E_A`. By Proposition 3
of the source (`MPSTensor.primitivity_tfae`), a trace-preserving family is
primitive exactly when it is normal, so the hypothesis here is `Kraus.IsNormal A`.
The bounds below do not use the trace-preserving normalization.

### Case (3): noninvertible one-step element with nonzero eigenvalue

Theorem 1 gives the case-(3) bound:
*if the one-step subspace `S₁(A) = Kraus.wordSpan A 1` contains a noninvertible matrix
with a nonzero eigenvalue, then `i(A) ≤ D²`.*

* `wordSpan_eq_top_of_isNormal_of_mem_wordSpan_one_of_noninvertible_eigenvector`:
  under normality, `X ∈ Kraus.wordSpan A 1`, noninvertibility of
  `X`, and eigenvector data `φ ≠ 0`, `μ ≠ 0`, we prove
  `Kraus.wordSpan A (D ^ 2) = ⊤`.

* `iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector`:
  the corresponding numeric bound `iIndex A ≤ D ^ 2`.

The single-Kraus statements
`wordSpan_eq_top_of_isNormal_of_noninvertible_eigenvector` and
`iIndex_le_sq_of_noninvertible_eigenvector` are corollaries.

### Case (2): invertible one-step element

Theorem 1 also gives the case-(2) bound:
*if `Kraus.wordSpan A 1` contains an invertible matrix, then
`i(A) ≤ D² − krausRank(A) + 1`.*

* `wordSpan_eq_top_of_isNormal_of_mem_wordSpan_one_of_isUnit`:
  under normality, `X ∈ Kraus.wordSpan A 1`, and `IsUnit X`, we
  prove `Kraus.wordSpan A (D ^ 2 - krausRank A + 1) = ⊤`.

* `iIndex_le_of_mem_wordSpan_one_of_isUnit`:
  the corresponding numeric bound
  `iIndex A ≤ D ^ 2 - krausRank A + 1`.

The single-Kraus statements are `wordSpan_eq_top_of_isNormal_of_isUnit`
and `iIndex_le_of_isNormal_of_isUnit` of `SpanGrowth/InvertibleWordSpan.lean`. The
proofs add the chosen one-step element as a redundant generator and use the
word-span invariance lemmas from that file.

Within TNLean these results are standalone Wielandt inequality statements:
the canonical-form, fundamental-theorem, and BNT development does not import
them directly.

This file is the preferred entry point for the currently formalized Theorem 1
bounds. The positive-definite primitive-to-normal theorem lives in
`TNLean.MPS.Transfer.Primitivity.Definitions`; it is not the
Theorem 1 bound itself.

The comparison `q(E_A) ≤ i(A)` of Proposition 1 is
`qIndex_le_iIndex_of_tracePreserving` in `Primitivity/Equivalence.lean`.

### Case (1): general bound

* `iIndex_le_general_of_isNormal`:
  the full general bound `i(A) ≤ (D² − krausRank(A) + 1) · D²`.

The proof uses the blocking trick: the sharp Lemma 1 word product of length
`n ≤ D² − krausRank(A) + 1` becomes a Kraus operator of the `n`-blocked tensor.
Writing `B` for `Kraus.block A n` with numbered words, the blocked invertible case uses case (2)
to get `Kraus.wordSpan B (D² - krausRank B + 1) = ⊤`, which is then padded to level `D²`.
The blocked noninvertible case uses case (3) to get `Kraus.wordSpan B (D²) = ⊤`
directly. Transferring the blocked conclusion back to the original tensor
yields the general bound.

The proof handles the edge case where all Kraus operators are nilpotent
(no Kraus operator has a nonzero eigenvalue) by using the positive-length
strengthening of Lemma 1: for `D ≥ 2`, the positive-level cumulative span of
positive-length words reaches `M_D(ℂ)` by the sharp bound, so there is always a
positive-length word with nonzero trace within that range.

It also contains the following results.

* `MPSTensor.exists_nonzero_trace_word_of_isNormal_sharp`,
  `MPSTensor.exists_nonzero_trace_word_of_isNormal_sharp_pos`: Lemma 1 — nonzero-trace word
  (arXiv:0909.5347).

## References

* [SPGWC09] Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347, Theorem 1
* [Wolf12] Wolf, *Quantum Channels & Operations*, Theorem 6.9

## Lemma 2(a) for MPS tensors

This file retains the MPS formulation of Lemma 2(a) from
Sanz--Pérez-García--Wolf--Cirac, *A quantum version of Wielandt's inequality*
(arXiv:0909.5347). Its finite-Kraus content is proved in
`Kraus.vectorSpreadSpan_eq_top_of_isNormal_of_eigenvector`.
-/

section NonzeroTraceWord

/-!
## Lemma 1 — nonzero-trace word (arXiv:0909.5347)

This file states the formal version of **Lemma 1** from
Sanz–Pérez-García–Wolf–Cirac, *A quantum version of Wielandt's inequality*
(arXiv:0909.5347), and the corresponding discussion in Wolf's Chapter 6.
The source's hypothesis is a primitive channel; by its Proposition 3
(`MPSTensor.primitivity_tfae`) a trace-preserving family is primitive exactly
when it is normal, and the statements below need only normality.

### Main results

* `exists_nonzero_trace_word_of_isNormal_sharp`:
  (sharp) if `A` is normal, then there
  exists a word product of length ≤ D² − krausRank(A) + 1 with nonzero trace.
  This is the exact bound from Lemma 1 of arXiv:0909.5347.

* `exists_nonzero_trace_word_of_isNormal_sharp_pos`:
  for positive `D`, there is a positive-length word of length
  ≤ D² − krausRank(A) + 1 with nonzero trace. The proof uses the
  positive-level cumulative span of positive-length words: once this span is all
  of `M_D(ℂ)`, the identity matrix is a linear combination of positive-length
  word products, so one of them has nonzero trace.

### Proof strategy

Apply the nonzero-trace result from `NonzeroTraceProduct.lean` at a length
witnessing normality.

These statements record Lemma 1 of arXiv:0909.5347 / Wolf Section 6.9
in the notation of the source; the FT/BNT formalization does not use them.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-- **Lemma 1, sharp version**.

If `A` is normal, then there exists a
word `w` with `|w| ≤ D² − krausRank(A) + 1` such that `tr (Kraus.evalWord A w) ≠ 0`.

This is the exact quantitative bound from Lemma 1 of arXiv:0909.5347:
"If E_A is primitive, then there exists A^(n) ∈ S_n(A) with
n ≤ D² − d + 1 such that tr(A^(n)) ≠ 0."

The paper uses the explicit parameter `d` (number of Kraus operators), but
dim(S₁(A)) ≤ d in general, and `krausRank A = dim(S₁(A))` is the
tight quantity. When `{A₁,…,Aₐ}` is a minimal Kraus family (linearly
independent), `krausRank A = d` and the bounds coincide.

Paper: arXiv:0909.5347, Lemma 1; Wolf, Chapter 6.
-/
theorem exists_nonzero_trace_word_of_isNormal_sharp [NeZero D]
    (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) :
    ∃ w : List (Fin d),
      w.length ≤ D ^ 2 - krausRank A + 1 ∧
      Matrix.trace (Kraus.evalWord A w) ≠ 0 := by
  obtain ⟨N, _, hN⟩ := hN
  exact Kraus.exists_nonzero_trace_word_sharp A hN

/-- **Lemma 1, sharp positive-length version**.

For positive `D`, if `A` is normal, then
there exists a **positive-length** word `w` with `|w| ≤ D² − krausRank(A) + 1`
such that `tr(Kraus.evalWord A w) ≠ 0`.

This strengthens `exists_nonzero_trace_word_of_isNormal_sharp` by
additionally requiring `1 ≤ w.length`, which is needed for the blocking
argument in Theorem 1 case (1). Equivalently, the positive-level cumulative
span of positive-length words reaches `⊤` by this sharp bound, so `1` is a
linear combination of positive-length word products; since `tr(1) = D ≠ 0`,
one of those products has nonzero trace.

Paper: arXiv:0909.5347, Lemma 1 (positive-length strengthening).
-/
theorem exists_nonzero_trace_word_of_isNormal_sharp_pos [NeZero D]
    (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) :
    ∃ w : List (Fin d),
      1 ≤ w.length ∧
      w.length ≤ D ^ 2 - krausRank A + 1 ∧
      Matrix.trace (Kraus.evalWord A w) ≠ 0 := by
  obtain ⟨N, hNpos, hN⟩ := hN
  exact Kraus.exists_nonzero_trace_word_sharp_pos A hN hNpos

end MPSTensor

end NonzeroTraceWord

section Bounds

section

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor
open Kraus (blockPhysDim)

namespace MPSTensor

variable {d D : ℕ}

/-! ## Part 1: Case (3) — noninvertible with nonzero eigenvalue gives `D²` -/

/-- **Theorem 1, case (3)**: under the paper-faithful one-step subspace
noninvertible eigenvalue hypotheses, `Kraus.wordSpan A (D ^ 2) = ⊤`.

If `A` is normal, and some arbitrary
matrix `X ∈ S₁(A) = Kraus.wordSpan A 1` is noninvertible and has a nonzero eigenvalue
with eigenvector `φ ≠ 0`, then the exact word span at level `D ^ 2` is the full
matrix algebra.

The proof adds `X` as a redundant first generator. Since `X ∈ S₁(A)`, this does
not change any exact word span or the Kraus rank; it only lets us apply the
single-generator theorem with `X` as the distinguished first entry.

Paper: arXiv:0909.5347, Theorem 1 case (3); Wolf, Theorem 6.9.
-/
theorem wordSpan_eq_top_of_isNormal_of_mem_wordSpan_one_of_noninvertible_eigenvector
    [NeZero D]
    (A : MPSTensor d D)
    (hN : Kraus.IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ Kraus.wordSpan A 1)
    (hNotInv : ¬ IsUnit (toLin' X))
    {φ : Fin D → ℂ} {μ : ℂ} (hφ : φ ≠ 0) (hμ : μ ≠ 0)
    (heig : X *ᵥ φ = μ • φ) :
    Kraus.wordSpan A (D ^ 2) = ⊤ := by
  let B : MPSTensor (d + 1) D := Kraus.oneStepAugment A X
  have hNB : Kraus.IsNormal B := by
    simpa [B] using isNormal_oneStepAugment_of_mem_wordSpan_one A hX hN
  have heigB : B (0 : Fin (d + 1)) *ᵥ φ = μ • φ := by
    simpa [B, Kraus.oneStepAugment] using heig
  have hNotInvB : ¬ IsUnit (toLin' (B (0 : Fin (d + 1)))) := by
    simpa [B, Kraus.oneStepAugment] using hNotInv
  have hCum : Kraus.cumulativeVectorSpan B φ (D - 1) = ⊤ :=
    eigenvector_spreading B φ hφ (0 : Fin (d + 1)) μ hμ heigB hNB
  have hVec : Kraus.vectorSpreadSpan B φ (D - 1) = ⊤ :=
    Kraus.vectorSpreadSpan_eq_top_of_cumulativeVectorSpan_eq_top_of_eigenvector
      B φ (D - 1) (0 : Fin (d + 1)) μ hμ heigB hCum
  have hRankOne : ∀ ψ : Fin D → ℂ,
      vecMulVec φ ψ ∈ Kraus.wordSpan B (D ^ 2 - D + 1) :=
    vecMulVec_eigenvector_exact_wordSpan B (0 : Fin (d + 1)) hNB hNotInvB hμ heigB
  have hBasis : ∀ j : Fin D,
      vecMulVec φ (Pi.single j (1 : ℂ)) ∈ Kraus.wordSpan B (D ^ 2 - D + 1) :=
    fun j => hRankOne (Pi.single j 1)
  have hAssembly : Kraus.wordSpan B ((D - 1) + (D ^ 2 - D + 1)) = ⊤ :=
    Kraus.wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis B φ hVec hBasis
  have hD_pos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hArith : (D - 1) + (D ^ 2 - D + 1) = D ^ 2 := by
    have hDD2 : D ≤ D ^ 2 := Nat.le_self_pow (by omega) D
    zify [hD_pos, hDD2]; ring
  have hBtop : Kraus.wordSpan B (D ^ 2) = ⊤ := by
    rwa [hArith] at hAssembly
  have hEq : Kraus.wordSpan B (D ^ 2) = Kraus.wordSpan A (D ^ 2) := by
    simpa [B] using Kraus.wordSpan_oneStepAugment_eq A hX (D ^ 2)
  rwa [hEq] at hBtop

/-- **Theorem 1, case (3)**: under the paper-faithful one-step subspace
noninvertible eigenvalue hypotheses, `iIndex A ≤ D ^ 2`.

Paper: arXiv:0909.5347, Theorem 1 case (3); Wolf, Theorem 6.9.
-/
theorem iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector
    [NeZero D]
    (A : MPSTensor d D)
    (hN : Kraus.IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ Kraus.wordSpan A 1)
    (hNotInv : ¬ IsUnit (toLin' X))
    {φ : Fin D → ℂ} {μ : ℂ} (hφ : φ ≠ 0) (hμ : μ ≠ 0)
    (heig : X *ᵥ φ = μ • φ) :
    iIndex A ≤ D ^ 2 := by
  have htop : Kraus.wordSpan A (D ^ 2) = ⊤ :=
    wordSpan_eq_top_of_isNormal_of_mem_wordSpan_one_of_noninvertible_eigenvector
      A hN hX hNotInv hφ hμ heig
  exact Nat.sInf_le
    (show D ^ 2 ∈ {n : ℕ | 0 < n ∧ Kraus.wordSpan A n = ⊤} from
      ⟨pow_pos (NeZero.pos D) 2, htop⟩)

/-- **Theorem 1, case (3)**: generator corollary of the one-step subspace theorem.

If `A` is normal, `A i₀` is not
invertible, and `φ ≠ 0` is an eigenvector of `A i₀` with eigenvalue `μ ≠ 0`,
then the exact word span at level `D ^ 2` is the full matrix algebra.

Paper: arXiv:0909.5347, Theorem 1 case (3); Wolf, Theorem 6.9.
-/
lemma wordSpan_eq_top_of_isNormal_of_noninvertible_eigenvector
    [NeZero D]
    (A : MPSTensor d D)
    (hN : Kraus.IsNormal A)
    (i₀ : Fin d)
    (hNotInv : ¬ IsUnit (toLin' (A i₀)))
    {φ : Fin D → ℂ} {μ : ℂ} (hφ : φ ≠ 0) (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    Kraus.wordSpan A (D ^ 2) = ⊤ := by
  exact
    wordSpan_eq_top_of_isNormal_of_mem_wordSpan_one_of_noninvertible_eigenvector
      A hN (Kraus.apply_mem_wordSpan_one A i₀) hNotInv hφ hμ heig

/-- **Theorem 1, case (3)**: generator corollary of the one-step subspace theorem.

Paper: arXiv:0909.5347, Theorem 1 case (3); Wolf, Theorem 6.9.
-/
lemma iIndex_le_sq_of_noninvertible_eigenvector
    [NeZero D]
    (A : MPSTensor d D)
    (hN : Kraus.IsNormal A)
    (i₀ : Fin d)
    (hNotInv : ¬ IsUnit (toLin' (A i₀)))
    {φ : Fin D → ℂ} {μ : ℂ} (hφ : φ ≠ 0) (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    iIndex A ≤ D ^ 2 := by
  exact
    iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector
      A hN (Kraus.apply_mem_wordSpan_one A i₀) hNotInv hφ hμ heig

/-! ## Part 2: Case (2) — invertible one-step subspace element -/

/-- **Theorem 1, case (2)**: under the paper-faithful one-step subspace
invertibility hypothesis, `Kraus.wordSpan A (D ^ 2 - krausRank A + 1) = ⊤`.

If `A` is normal and some arbitrary
matrix `X ∈ S₁(A) = Kraus.wordSpan A 1` is invertible, then the sharp case-(2)
word-length bound holds.

The proof adds `X` as a redundant first generator. This leaves every exact word
span and `krausRank` unchanged, and reduces the statement to the existing
single-generator invertible theorem.

Paper: arXiv:0909.5347, Theorem 1 case (2); Wolf, Theorem 6.9.
-/
theorem wordSpan_eq_top_of_isNormal_of_mem_wordSpan_one_of_isUnit
    (A : MPSTensor d D)
    (hN : Kraus.IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ Kraus.wordSpan A 1)
    (hInv : IsUnit X) :
    Kraus.wordSpan A (D ^ 2 - krausRank A + 1) = ⊤ := by
  let B : MPSTensor (d + 1) D := Kraus.oneStepAugment A X
  have hNB : Kraus.IsNormal B := by
    simpa [B] using isNormal_oneStepAugment_of_mem_wordSpan_one A hX hN
  have hInvB : IsUnit (B (0 : Fin (d + 1))) := by
    simpa [B, Kraus.oneStepAugment] using hInv
  have hKraus : krausRank B = krausRank A := by
    simpa [B] using krausRank_oneStepAugment A hX
  have hBtop : Kraus.wordSpan B (D ^ 2 - krausRank B + 1) = ⊤ :=
    wordSpan_eq_top_of_isNormal_of_isUnit B (0 : Fin (d + 1)) hInvB hNB
  have hBtop' : Kraus.wordSpan B (D ^ 2 - krausRank A + 1) = ⊤ := by
    simpa [hKraus] using hBtop
  have hEq : Kraus.wordSpan B (D ^ 2 - krausRank A + 1) =
      Kraus.wordSpan A (D ^ 2 - krausRank A + 1) := by
    simpa [B] using Kraus.wordSpan_oneStepAugment_eq A hX (D ^ 2 - krausRank A + 1)
  rwa [hEq] at hBtop'

/-- **Theorem 1, case (2)**: under the paper-faithful one-step subspace
invertibility hypothesis, `iIndex A ≤ D ^ 2 - krausRank A + 1`.

Paper: arXiv:0909.5347, Theorem 1 case (2); Wolf, Theorem 6.9.
-/
theorem iIndex_le_of_mem_wordSpan_one_of_isUnit
    (A : MPSTensor d D)
    (hN : Kraus.IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ Kraus.wordSpan A 1)
    (hInv : IsUnit X) :
    iIndex A ≤ D ^ 2 - krausRank A + 1 := by
  have htop : Kraus.wordSpan A (D ^ 2 - krausRank A + 1) = ⊤ :=
    wordSpan_eq_top_of_isNormal_of_mem_wordSpan_one_of_isUnit
      A hN hX hInv
  exact Nat.sInf_le
    (show D ^ 2 - krausRank A + 1 ∈
        {n : ℕ | 0 < n ∧ Kraus.wordSpan A n = ⊤} from ⟨by omega, htop⟩)

/-! ## Part 3: Case (1) — General bound via blocking

The full Wielandt bound combines sharp Lemma 1 (a word product of length
≤ D² − krausRank(A) + 1 has nonzero trace) with the blocking trick: the word
product becomes a Kraus operator of the `n`-blocked tensor. In the blocked
invertible case, case (2) gives a sharper level
`D² - krausRank (Kraus.block A n) + 1`, which is then padded to `D²`; in the
blocked noninvertible case, case (3) gives `Kraus.wordSpan (Kraus.block A n) (D²) = ⊤`
directly. This transfers to `Kraus.wordSpan A (D² · n) = ⊤`.

Paper: arXiv:0909.5347, Theorem 1 case (1); Wolf, Theorem 6.9. -/

/-- **Theorem 1, case (1)**: the general Wielandt bound
`iIndex A ≤ (D² − krausRank A + 1) · D²`.

Under normality:
1. By sharp Lemma 1, there exists a word `w` of length
   `n ≤ D² − krausRank(A) + 1` with `tr(Kraus.evalWord A w) ≠ 0`.
2. This matrix has a nonzero eigenvalue `μ` with eigenvector `φ`.
3. The `n`-blocked tensor `Kraus.block A n` has this matrix as a Kraus operator.
4. In the blocked invertible case, case (2) yields
   `Kraus.wordSpan (Kraus.block A n) (D² - krausRank (Kraus.block A n) + 1) = ⊤`,
   hence also `Kraus.wordSpan (Kraus.block A n) (D²) = ⊤`; in the blocked
   noninvertible case, case (3) gives `Kraus.wordSpan (Kraus.block A n) (D²) = ⊤`
   directly.
5. Transferring back: `Kraus.wordSpan A (D² · n) = ⊤`.
6. Hence `i(A) ≤ D² · n ≤ (D² − krausRank(A) + 1) · D²`.

Paper: arXiv:0909.5347, Theorem 1; Wolf, Theorem 6.9.
-/
theorem iIndex_le_general_of_isNormal [NeZero D]
    (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) :
    iIndex A ≤ (D ^ 2 - krausRank A + 1) * D ^ 2 := by
  have hD_pos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  exact (show iIndex A ≤ (D ^ 2 - krausRank A + 1) * D ^ 2 from by
    -- Get a **positive-length** sharp nonzero-trace word
    have hexists := exists_nonzero_trace_word_of_isNormal_sharp_pos A hN
    obtain ⟨w, hw_pos, hw_len, hw_tr⟩ := hexists
    -- Extract eigenvalue and eigenvector from this word
    obtain ⟨μ, φ, hμ, hφ, heig⟩ := exists_eigenvector_of_trace_ne_zero _ hw_tr
    set n := w.length with hn_def
    have hn_pos : 0 < n := hw_pos
    -- Number the blocks of length `n`; the case analysis below is stated for numbered letters.
    set e := Kraus.decodeBlockEquiv d n
    set B := Kraus.reindexPhysical e (Kraus.block A n)
    have hWS : ∀ k, Kraus.wordSpan B k = Kraus.wordSpan A (k * n) := fun k ↦ by
      rw [Kraus.wordSpan_eq_of_range_eq (K := B) (e.surjective.range_comp _), Kraus.wordSpan_block]
    -- B is Kraus.IsNormal
    have hNB : Kraus.IsNormal B :=
      (isNormal_reindexPhysical_equiv e _).2 (hN.block hn_pos)
    -- The blocked letter of w
    set σ₀ : Fin n → Fin d := w.get with hσ₀_def
    set i₀ := e.symm σ₀ with hi₀_def
    -- The Kraus operator B i₀ = Kraus.evalWord A w
    have hBi₀ : B i₀ = Kraus.evalWord A w := by
      simp [B, i₀, σ₀, Kraus.reindexPhysical, List.ofFn_get]
    -- The eigenvector equation transfers to B i₀
    have heigB : B i₀ *ᵥ φ = μ • φ := by rw [hBi₀]; exact heig
    -- Case split on invertibility
    by_cases hInv : IsUnit (B i₀)
    · -- B i₀ is invertible: apply case (2) to blocked tensor, then permanence
      have hInvTop := wordSpan_eq_top_of_isNormal_of_isUnit B i₀ hInv hNB
      -- Use permanence to extend to level D² (since D²-krausRank B+1 ≤ D²)
      have hD2top : Kraus.wordSpan B (D ^ 2) = ⊤ := by
        apply Kraus.wordSpan_eq_top_of_ge_of_isUnit B i₀ hInv hInvTop
        have hkB : krausRank B ≤ D ^ 2 := by
          simpa [krausRank] using Kraus.wordSpan_finrank_le B 1
        -- krausRank B ≥ 1 since B i₀ is a unit (hence nonzero) in Kraus.wordSpan B 1
        have hkB_pos : 1 ≤ krausRank B := by
          rw [krausRank, Nat.one_le_iff_ne_zero]
          intro h0
          have hbot := Submodule.finrank_eq_zero.mp h0
          have hBmem : B i₀ ∈ Kraus.wordSpan B 1 := by
            have := Kraus.evalWord_mem_wordSpan B ([i₀] : List (Fin (blockPhysDim d n)))
            simpa [Kraus.evalWord] using this
          rw [hbot] at hBmem
          change B i₀ = 0 at hBmem
          exact not_isUnit_zero (hBmem ▸ hInv)
        omega
      -- Transfer: Kraus.wordSpan A (D² * n) = ⊤
      have hAtop : Kraus.wordSpan A (D ^ 2 * n) = ⊤ := by rwa [hWS] at hD2top
      -- iIndex A ≤ D² * n ≤ D² * (D²-d'+1) = (D²-d'+1) * D²
      calc iIndex A ≤ D ^ 2 * n :=
          Nat.sInf_le ⟨Nat.mul_pos (pow_pos hD_pos 2) hn_pos, hAtop⟩
        _ ≤ D ^ 2 * (D ^ 2 - krausRank A + 1) := by
            apply Nat.mul_le_mul_left; exact hw_len
        _ = (D ^ 2 - krausRank A + 1) * D ^ 2 := Nat.mul_comm _ _
    · -- B i₀ is not invertible: apply case (3) to blocked tensor
      have hNotInv : ¬ IsUnit (toLin' (B i₀)) :=
        fun h => hInv (Matrix.isUnit_toLin'_iff.mp h)
      have hD2top : Kraus.wordSpan B (D ^ 2) = ⊤ :=
        wordSpan_eq_top_of_isNormal_of_noninvertible_eigenvector
          B hNB i₀ hNotInv hφ hμ heigB
      -- Transfer: Kraus.wordSpan A (D² * n) = ⊤
      have hAtop : Kraus.wordSpan A (D ^ 2 * n) = ⊤ := by rwa [hWS] at hD2top
      calc iIndex A ≤ D ^ 2 * n :=
          Nat.sInf_le ⟨Nat.mul_pos (pow_pos hD_pos 2) hn_pos, hAtop⟩
        _ ≤ D ^ 2 * (D ^ 2 - krausRank A + 1) := by
            apply Nat.mul_le_mul_left; exact hw_len
        _ = (D ^ 2 - krausRank A + 1) * D ^ 2 := Nat.mul_comm _ _)

end MPSTensor

end

section

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

end MPSTensor

end

end Bounds
