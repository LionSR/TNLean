/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixNonzeroTraceEigenvalue
import TNLean.Kraus.Wielandt.SpanGrowth.NonzeroTraceProduct

/-!
# Eigenvectors from finite-family word products

A full exact word span supplies a bounded word product with nonzero trace. Such a product has a
nonzero eigenvalue and a corresponding nonzero eigenvector.
-/

open scoped Matrix
open MPSTensor

namespace Kraus

variable {d D : ℕ}

/-- If an exact word span is full, some word of length at most `D ^ 2` evaluates to a matrix with
a nonzero eigenvalue and a corresponding nonzero eigenvector.

The coarse length bound and exact-span hypothesis are inherited from
`exists_nonzero_trace_word`, where their relation to the paper is documented.

Paper: arXiv:0909.5347, Theorem 1 proof, first paragraph. -/
theorem exists_word_eigenvector [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ}
    (hN : wordSpan K N = ⊤) :
    ∃ (w₀ : List (Fin d)) (μ : ℂ) (φ : Fin D → ℂ),
      w₀.length ≤ D ^ 2 ∧
      μ ≠ 0 ∧
      φ ≠ 0 ∧
      evalWord K w₀ *ᵥ φ = μ • φ := by
  obtain ⟨w₀, hw₀_len, hw₀_tr⟩ := exists_nonzero_trace_word K hN
  obtain ⟨μ, φ, hμ, hφ, heig⟩ := exists_eigenvector_of_trace_ne_zero _ hw₀_tr
  exact ⟨w₀, μ, φ, hw₀_len, hμ, hφ, heig⟩

end Kraus
