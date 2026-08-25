/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.SpanGrowth.CumulativeToWordSpan
import TNLean.Wielandt.SpanGrowth.CumulativeSpan
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan
import TNLean.Algebra.BurnsideMatrix
import QICLean.Algebra.BurnsideTheorem

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
* `Kraus.exists_eigenvector_of_cumulativeSpan_eq_top` extracts a nonzero-eigenvalue
  eigenvector from a word with nonzero trace.

## References

* arXiv:0909.5347, Proposition 3
* arXiv:1606.00608, Section 2.3
-/

open scoped Matrix
open MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-! ## MPS-specific consequences -/

/-- PGVWC07 injectivity propagation: for a right-normalized tensor, block
injectivity at length `L` implies block injectivity at every length `m ≥ L`. -/
theorem isNBlkInjective_of_ge_of_unital
    (A : MPSTensor d D)
    (hUnital : ∑ a : Fin d, A a * (A a)ᴴ = 1)
    {L m : ℕ} (hL : Kraus.IsNBlkInjective A L) (hm : L ≤ m) :
    Kraus.IsNBlkInjective A m := by
  rw [← wordSpan_eq_top_iff_isNBlkInjective] at hL ⊢
  exact Kraus.wordSpan_eq_top_of_ge_of_unital A hUnital hL hm

/-- If `Kraus.cumulativeSpan A N = ⊤` and the identity belongs to the one-letter span,
then `A` is normal. -/
theorem isNormal_of_cumulativeSpan_eq_top_of_aperiodic
    (A : MPSTensor d D) {N : ℕ}
    (hcs : Kraus.cumulativeSpan A N = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Kraus.wordSpan A 1) :
    Kraus.IsNormal A := by
  refine ⟨N + 1, Nat.zero_lt_succ N, ?_⟩
  rw [← wordSpan_eq_top_iff_isNBlkInjective]
  rw [← Kraus.cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one A hone]
  exact eq_top_iff.mpr (hcs.ge.trans (Kraus.cumulativeSpan_mono A N))

/-- If the generated matrix algebra is full and the identity belongs to the
one-letter span, then `A` is normal. -/
theorem isNormal_of_algSpan_eq_top_of_aperiodic
    (A : MPSTensor d D)
    (halg : Matrix.algSpan A = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Kraus.wordSpan A 1) :
    Kraus.IsNormal A := by
  obtain ⟨N, hN⟩ := exists_cumulativeSpan_eq_top_of_algSpan_eq_top A halg
  exact isNormal_of_cumulativeSpan_eq_top_of_aperiodic A hN hone

end MPSTensor
