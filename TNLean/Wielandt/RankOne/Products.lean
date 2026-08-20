/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Wielandt.RankOne.Products
import TNLean.Kraus.Injectivity

/-!
# Eigenvectors from Wielandt word products

The finite-family result is defined in namespace `Kraus`. This module preserves the established
tensor-network theorem name and statement as an equivalent formulation.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Equivalent formulation for extracting a nonzero eigenvector from a bounded word product.

Paper: arXiv:0909.5347, Theorem 1 proof, first paragraph. -/
theorem exists_word_eigenvector [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    ∃ (w₀ : List (Fin d)) (μ : ℂ) (φ : Fin D → ℂ),
      w₀.length ≤ D ^ 2 ∧
      μ ≠ 0 ∧
      φ ≠ 0 ∧
      evalWord A w₀ *ᵥ φ = μ • φ := by
  obtain ⟨N, _, hN⟩ := hN
  exact Kraus.exists_word_eigenvector A hN

end MPSTensor
