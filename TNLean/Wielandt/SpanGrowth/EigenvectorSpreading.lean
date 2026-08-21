/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.SpanGrowth.EigenvectorSpreading
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Eigenvector spreading for MPS tensors

This file preserves the established MPS tensor interface to the transfer-free
vector-spreading results in `Kraus` and proves the normal-tensor specialization.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- **Lemma 2(a)**: If the channel is normal and `A` has an eigenvector
with nonzero eigenvalue, then `K_{D-1}(A, φ) = ℂ^D`.

Paper: `H_{D-1}(A, φ) = ℂ^D` (arXiv:0909.5347, Lemma 2(a)).

Deviation: we prove the cumulative conclusion `K_{D-1} = ⊤` instead of the paper's
single-level conclusion `H_{D-1} = ⊤`. This is enough for every downstream use in this
formalization.

The eigenvector data are kept in the statement to match the paper and downstream
theorems. The current cumulative proof uses only `hφ` together with
the normality witness. -/
theorem eigenvector_spreading [NeZero D]
    (A : MPSTensor d D) (φ : Fin D → ℂ) (hφ : φ ≠ 0)
    (_i₀ : Fin d) (_μ : ℂ) (_hμ : _μ ≠ 0)
    (_heig : A _i₀ *ᵥ φ = _μ • φ)
    (hNormal : IsNormal A) :
    Kraus.cumulativeVectorSpan A φ (D - 1) = ⊤ := by
  obtain ⟨N, hN⟩ := cumulativeSpan_eq_top_of_isNormal A hNormal
  exact Kraus.eigenvector_spreading_of_cumulativeSpan_eq_top A φ hφ hN

end MPSTensor
