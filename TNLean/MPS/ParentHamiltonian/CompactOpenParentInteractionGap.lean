/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CompactOpenParentGap
import TNLean.MPS.ParentHamiltonian.Martingale.OpenParentInteractionGap

/-!
# Compact open-chain gaps for positive parent interactions

A compact continuous family of simultaneously injective blocks has a common
positive canonical open-chain gap at each range strictly larger than the
simultaneous injectivity length. Continuous positive interactions with the
same local kernels inherit this gap. The local lower comparison constant is
uniform on the compact set; a pointwise upper comparison identifies the open
kernels. Nonzero block weights need not vary continuously.

For pairwise inequivalent normalized normal blocks, the dimension bound
supplies the simultaneous injectivity length, so no such length is assumed.

Source: arXiv:1010.3732, Appendix A, lines 2475--2580, for compactness and
positive interactions; arXiv:2011.12127, lines 2170--2172, for local positive
comparison; Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
for the open-chain gap.

**Scope restriction (sufficient interaction range):** The supplied-span theorem
assumes \(R\geq S+1\), and the normal-block corollary assumes the sufficient
dimension bound. Neither assertion restricts the source definition of a
parent interaction. The unrestricted shorter-range assertion and its
counterexample are recorded in
`docs/paper-gaps/cpgsv21_short_range_parent_gap.tex`.
-/

open scoped Topology

namespace MPSTensor

/-- Continuous positive parent interactions for a compact family of several
simultaneously injective blocks have a gap uniform in the parameter and all
admissible open-chain lengths. Nonzero weights need not be continuous.
Source: arXiv:1010.3732, Appendix A; Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem exists_uniform_block_openParentInteraction_gap_of_compact
    {X : Type*} [TopologicalSpace X] {d r : ℕ} {dim : Fin r → ℕ}
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    {S R : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    (hR : S + 1 ≤ R)
    (H : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hH : Continuous H)
    (hParent : ∀ x, IsParentInteraction
      (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R (H x).toLinearMap)
    {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES (H x).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES (H x).toLinearMap N v‖ := by
  have hSpanR (x : X) : WordTupleSpanTop (A x) R :=
    wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega)
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_uniform_openParentHamiltonianES_toTensorFromBlocks_gap_of_compact_all_lengths
      μ A hμ hA hS hSpan hR hK
  exact exists_uniform_openInteractionHamiltonianES_gap_of_compact_canonical_gap
    (fun x => toTensorFromBlocks (d := d) (μ := μ x) (A x))
    (continuous_groundSpaceES_toTensorFromBlocks_starProjection_family μ A hμ hA R hSpanR)
    H hH hParent hK (by omega) hγ hGap

/-- A compact continuous family of pairwise inequivalent normalized normal
blocks has one positive open-chain gap for continuous positive interactions at
every range at least \(3\max(\sum_jD_j,1)^5\). The simultaneous injectivity
length is derived from the dimensions. Source: arXiv:1606.00608, lines
317--345; arXiv:1010.3732, Appendix A; Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem exists_uniform_block_openParentInteraction_gap_of_compact_isNormalTensor
    {X : Type*} [TopologicalSpace X] {d r : ℕ} {dim : Fin r → ℕ}
    [NeZero d]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    (hNormal : ∀ x j, IsNormalTensor (A x j))
    (hDistinct : ∀ x, BlocksNotGaugePhaseEquiv (A x)) {R : ℕ}
    (hR : 3 * (max (∑ j, dim j) 1) ^ 5 ≤ R)
    (H : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hH : Continuous H)
    (hParent : ∀ x, IsParentInteraction
      (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R (H x).toLinearMap)
    {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES (H x).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES (H x).toLinearMap N v‖ := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · let := hX
    exact ⟨1, zero_lt_one, fun x => isEmptyElim x⟩
  let : ∀ j, NeZero (dim j) :=
    fun j => ⟨(hNormal (Classical.choice hX) j).bondDim_ne_zero⟩
  have hCap : 0 < max (∑ j, dim j) 1 :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hSpanR (x : X) : WordTupleSpanTop (A x) R := by
    obtain ⟨S, hS, hBound, hSpan⟩ :=
      exists_positive_wordTupleSpanTop_succ_le_three_cap_pow_five_of_isNormalTensor
        (A x) hCap (le_max_left _ _) (hNormal x) (hDistinct x)
    exact wordTupleSpanTop_of_ge (A x) hS hSpan (by omega)
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_uniform_block_openParentHamiltonianES_gap_of_compact_isNormalTensor
      μ A hμ hA hNormal hDistinct hR hK
  exact exists_uniform_openInteractionHamiltonianES_gap_of_compact_canonical_gap
    (fun x => toTensorFromBlocks (d := d) (μ := μ x) (A x))
    (continuous_groundSpaceES_toTensorFromBlocks_starProjection_family μ A hμ hA R hSpanR)
    H hH hParent hK (lt_of_lt_of_le (by positivity) hR) hγ hGap

end MPSTensor
