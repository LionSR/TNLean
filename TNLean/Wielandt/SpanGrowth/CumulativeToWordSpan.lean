/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Wielandt.SpanGrowth.CumulativeToWordSpan
import TNLean.Wielandt.SpanGrowth.CumulativeSpan
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan
import TNLean.Algebra.BurnsideMatrix
import TNLean.Algebra.BurnsideTheorem

/-!
# From cumulative span to word span for MPS tensors

This file gives the MPS-facing consequences of the generic Kraus-family span
results. The transfer-free statements are MPS restatements of the corresponding
Kraus-family results. The MPS-specific results connect exact
word-span fullness to block injectivity and normality.

## Main results

* `isNBlkInjective_of_ge_of_unital` propagates block injectivity under the
  equation $\sum_a A_a A_a^\dagger=I$.
* `isNormal_of_cumulativeSpan_eq_top_of_aperiodic` derives normality from full
  cumulative span and identity membership in the one-letter span.
* `isNormal_of_algSpan_eq_top_of_aperiodic` combines this with algebra-span
  fullness.
* `exists_eigenvector_of_cumulativeSpan_eq_top` extracts a nonzero-eigenvalue
  eigenvector from a word with nonzero trace.

## References

* arXiv:0909.5347, Proposition 3
* arXiv:1606.00608, Section 2.3
-/

open scoped Matrix
open MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-! ## MPS restatements of transfer-free span results -/

/-- If the cumulative span is full, some word of bounded length has nonzero trace. -/
theorem exists_nonzero_trace_word_of_cumulativeSpan_eq_top [NeZero D]
    (A : MPSTensor d D) {N : ℕ} (hcs : cumulativeSpan A N = ⊤) :
    ∃ w : List (Fin d), w.length ≤ N ∧ Matrix.trace (evalWord A w) ≠ 0 :=
  Kraus.exists_nonzero_trace_word_of_cumulativeSpan_eq_top A hcs

/-- Identity membership at length `L` embeds each exact word span into the span
`L` steps later. -/
theorem wordSpan_mono_of_one_mem_wordSpan
    (A : MPSTensor d D) {L : ℕ}
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A L) :
    ∀ n, wordSpan A n ≤ wordSpan A (n + L) :=
  Kraus.wordSpan_mono_of_one_mem_wordSpan A hone

/-- Identity membership in the one-letter span makes every exact word span
contained in its successor. -/
theorem wordSpan_mono_succ_of_one_mem_wordSpan_one
    (A : MPSTensor d D)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    ∀ n, wordSpan A n ≤ wordSpan A (n + 1) :=
  Kraus.wordSpan_mono_succ_of_one_mem_wordSpan_one A hone

/-- Identity membership in the one-letter span makes exact word spans
monotone. -/
theorem wordSpan_mono'_of_one_mem_wordSpan_one
    (A : MPSTensor d D)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1)
    {n m : ℕ} (hnm : n ≤ m) :
    wordSpan A n ≤ wordSpan A m :=
  Kraus.wordSpan_mono'_of_one_mem_wordSpan_one A hone hnm

/-- Under $\sum_a A_a A_a^\dagger=I$, fullness of the length-`n` word span
propagates to length `n + 1`. -/
theorem wordSpan_succ_eq_top_of_unital_of_wordSpan_eq_top
    (A : MPSTensor d D)
    (hUnital : ∑ a : Fin d, A a * (A a)ᴴ = 1)
    {n : ℕ} (hTop : wordSpan A n = ⊤) :
    wordSpan A (n + 1) = ⊤ :=
  Kraus.wordSpan_succ_eq_top_of_unital_of_wordSpan_eq_top A hUnital hTop

/-- Under $\sum_a A_a A_a^\dagger=I$, fullness at length `L` propagates to every
length `m ≥ L`. -/
theorem wordSpan_eq_top_of_ge_of_unital
    (A : MPSTensor d D)
    (hUnital : ∑ a : Fin d, A a * (A a)ᴴ = 1)
    {L m : ℕ} (hL : wordSpan A L = ⊤) (hm : L ≤ m) :
    wordSpan A m = ⊤ :=
  Kraus.wordSpan_eq_top_of_ge_of_unital A hUnital hL hm

/-- Identity membership in the one-letter span identifies cumulative and exact
word spans at every length. -/
theorem cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one
    (A : MPSTensor d D)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    ∀ n, cumulativeSpan A n = wordSpan A n :=
  Kraus.cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one A hone

/-! ## MPS-specific consequences -/

/-- PGVWC07 injectivity propagation: for a right-normalized tensor, block
injectivity at length `L` implies block injectivity at every length `m ≥ L`. -/
theorem isNBlkInjective_of_ge_of_unital
    (A : MPSTensor d D)
    (hUnital : ∑ a : Fin d, A a * (A a)ᴴ = 1)
    {L m : ℕ} (hL : IsNBlkInjective A L) (hm : L ≤ m) :
    IsNBlkInjective A m := by
  rw [← wordSpan_eq_top_iff_isNBlkInjective] at hL ⊢
  exact wordSpan_eq_top_of_ge_of_unital A hUnital hL hm

/-- If `cumulativeSpan A N = ⊤` and the identity belongs to the one-letter span,
then `A` is normal. -/
theorem isNormal_of_cumulativeSpan_eq_top_of_aperiodic
    (A : MPSTensor d D) {N : ℕ}
    (hcs : cumulativeSpan A N = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    IsNormal A := by
  refine ⟨N + 1, Nat.zero_lt_succ N, ?_⟩
  rw [← wordSpan_eq_top_iff_isNBlkInjective]
  rw [← cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one A hone]
  exact eq_top_iff.mpr (hcs.ge.trans (cumulativeSpan_mono A N))

/-- If the generated matrix algebra is full and the identity belongs to the
one-letter span, then `A` is normal. -/
theorem isNormal_of_algSpan_eq_top_of_aperiodic
    (A : MPSTensor d D)
    (halg : Matrix.algSpan A = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    IsNormal A := by
  obtain ⟨N, hN⟩ := exists_cumulativeSpan_eq_top_of_algSpan_eq_top A halg
  exact isNormal_of_cumulativeSpan_eq_top_of_aperiodic A hN hone

/-! ## Eigenvector extraction from a nonzero-trace word -/

/-- Full cumulative span gives a bounded-length word with an eigenvector whose
eigenvalue is nonzero.

Paper anchor: proof of Theorem 1, case (1) in arXiv:0909.5347. -/
theorem exists_eigenvector_of_cumulativeSpan_eq_top [NeZero D]
    (A : MPSTensor d D) {N : ℕ} (hcs : cumulativeSpan A N = ⊤) :
    ∃ (w : List (Fin d)) (μ : ℂ) (φ : Fin D → ℂ),
      w.length ≤ N ∧ μ ≠ 0 ∧ φ ≠ 0 ∧
      evalWord A w *ᵥ φ = μ • φ :=
  Kraus.exists_eigenvector_of_cumulativeSpan_eq_top A hcs

end MPSTensor
