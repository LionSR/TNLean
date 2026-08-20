/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixFittingRange
import TNLean.Analysis.MatrixNonzeroTraceEigenvalue
import TNLean.Wielandt.SpanGrowth.NonzeroTraceProduct

/-!
# Eigenvectors from Wielandt word products

This file combines the neutral nonzero-trace eigenvector API with the bounded nonzero-trace
word supplied by normality. The underlying matrix and Fitting results live in `TNLean.Analysis`.
-/

open scoped Matrix
open Polynomial Module

namespace MPSTensor

open MPSTensor

variable {d D : ℕ}

/-- **Given a word with nonzero trace, extract an eigenvalue and eigenvector.**

This combines `exists_nonzero_trace_word` with `exists_eigenvector_of_trace_ne_zero`
to get a word `w₀`, its eigenvalue `μ ≠ 0`, and eigenvector `φ ≠ 0` such that
`evalWord A w₀ *ᵥ φ = μ • φ`.

Paper: arXiv:0909.5347, Theorem 1 proof, first paragraph. -/
theorem exists_word_eigenvector [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    ∃ (w₀ : List (Fin d)) (μ : ℂ) (φ : Fin D → ℂ),
      w₀.length ≤ D ^ 2 ∧
      μ ≠ 0 ∧
      φ ≠ 0 ∧
      evalWord A w₀ *ᵥ φ = μ • φ := by
  obtain ⟨w₀, hw₀_len, hw₀_tr⟩ := exists_nonzero_trace_word A hN
  obtain ⟨μ, φ, hμ, hφ, heig⟩ := exists_eigenvector_of_trace_ne_zero _ hw₀_tr
  exact ⟨w₀, μ, φ, hw₀_len, hμ, hφ, heig⟩

end MPSTensor
