/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVSharpBlocking

/-!
# Bounded simultaneous injective blocking of normal blocks

Pairwise gauge-phase inequivalent normalized normal blocks have a positive
blocking length after which their matrices span the direct sum of all block
matrix algebras. The bound depends only on the sum of the bond dimensions.

Source: arXiv:1606.00608, lines 317--345. This is the initial simultaneous
blocking used in arXiv:1010.3732, lines 575--597 and Appendix A.
-/

open scoped BigOperators

namespace MPSTensor

/-- Pairwise gauge-phase inequivalent normalized normal blocks have a
simultaneous one-site span after blocking at a positive length
\(L\) satisfying \(L+1\leq3\max(\sum_jD_j,1)^5\).
Source: arXiv:1606.00608, lines 317--345; arXiv:1010.3732, lines 575--597. -/
theorem exists_positive_blockTensor_wordTupleSpanTop_one_of_isNormalTensor
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hNormal : ∀ j, IsNormalTensor (A j)) (hDistinct : BlocksNotGaugePhaseEquiv A) :
    ∃ L : ℕ, 0 < L ∧ L + 1 ≤ 3 * (max (∑ j, dim j) 1) ^ 5 ∧
      WordTupleSpanTop (fun j => blockTensor (A j) L) 1 := by
  obtain ⟨L, hL, hBound, hSpan⟩ :=
    exists_positive_wordTupleSpanTop_succ_le_three_cap_pow_five_of_isNormalTensor
      A (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (le_max_left _ _) hNormal hDistinct
  exact ⟨L, hL, hBound, wordTupleSpanTop_blockTensor_one A hSpan⟩

end MPSTensor
