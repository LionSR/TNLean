/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVSharpBlocking
import TNLean.MPS.ParentHamiltonian.Martingale.BlockOpenGapAllLengths

/-!
# Open-chain gaps for normal blocks at a dimension bound

Pairwise inequivalent normal blocks of total bond dimension \(D\) have a
simultaneous injectivity length \(S\) with \(S+1\leq3\max(D,1)^5\).
The all-length open-chain theorem therefore applies at every interaction
range above this dimension bound, without a supplied injectivity length.

Source: arXiv:1606.00608, lines 317--345; Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6.

**Scope restriction (sufficient interaction range):** The dimension bound is
sufficient and need not be optimal. The sharper theorem assumes
\(R\geq S+1\) at an actual simultaneous injectivity length. The restriction
is documented in `docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`.
-/

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d]

/-- Pairwise inequivalent normal blocks have a uniform open-chain gap at
range at least \(3\max(\sum_jD_j,1)^5\), for every chain containing an
interaction. Normalization and an injectivity length are derived internally.
Source: arXiv:1606.00608, lines 317--345; Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem exists_openParentHamiltonianES_toTensorFromBlocks_gap_of_isNormalTensor
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hNormal : ∀ j, IsNormalTensor (A j))
    (hDistinct : BlocksNotGaugePhaseEquiv A) {R : ℕ}
    (hR : 3 * (max (∑ j, dim j) 1) ^ 5 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, R ≤ N → ∀ v ∈
      (groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N)ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ) A) R N v‖ := by
  let : ∀ j, NeZero (dim j) := fun j ↦ ⟨(hNormal j).bondDim_ne_zero⟩
  obtain ⟨S, hS, hBound, hSpan⟩ :=
    exists_positive_wordTupleSpanTop_succ_le_three_cap_pow_five_of_isNormalTensor A
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (le_max_left _ _) hNormal hDistinct
  exact exists_openParentHamiltonianES_toTensorFromBlocks_gap_of_wordTupleSpanTop
    μ A hμ hS hSpan (hBound.trans hR)

end MPSTensor
