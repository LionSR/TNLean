/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixFittingRange
import TNLean.Kraus.Wielandt.RankOne.Extraction

/-!
# Rank-one extraction compatibility module

The Fitting range description formerly proved here now lives in
`TNLean.Analysis.MatrixFittingRange`. The exact-span extraction results are restated from their
finite-family versions. This module retains the established import surface for downstream rank-one
extraction files.

## References

- arXiv:0909.5347, Theorem 1 proof, first paragraph
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- If `wordSpan A N = ⊤` and `[NeZero D]`, then there exists a word function
`σ : Fin N → Fin d` such that `tr(evalWord A (List.ofFn σ)) ≠ 0`. -/
theorem exists_nonzero_trace_word_of_wordSpan_eq_top [NeZero D]
    (A : MPSTensor d D) {N : ℕ} (htop : wordSpan A N = ⊤) :
    ∃ σ : Fin N → Fin d, (evalWord A (List.ofFn σ)).trace ≠ 0 := by
  exact Kraus.exists_nonzero_trace_word_of_wordSpan_eq_top A htop

/-- If `wordSpan A N = ⊤` and `[NeZero D]`, then there exists a word function
`σ : Fin N → Fin d` with `evalWord A (List.ofFn σ)` having a nonzero eigenvalue
and eigenvector. -/
theorem exists_eigenvector_of_wordSpan_eq_top [NeZero D]
    (A : MPSTensor d D) {N : ℕ} (htop : wordSpan A N = ⊤) :
    ∃ (σ : Fin N → Fin d) (μ : ℂ) (φ : Fin D → ℂ),
      μ ≠ 0 ∧ φ ≠ 0 ∧
      evalWord A (List.ofFn σ) *ᵥ φ = μ • φ := by
  exact Kraus.exists_eigenvector_of_wordSpan_eq_top A htop

end MPSTensor
