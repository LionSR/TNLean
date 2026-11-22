/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockWordSpanSeparation
import TNLean.MPS.ParentHamiltonian.BlockWordSpanNormalization
import TNLean.MPS.ParentHamiltonian.BlockWordSpanPropagation
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockGapThreshold

/-!
# A uniform gap at the simultaneous block-injectivity range

The supplied simultaneous injectivity length is retained: every canonical
periodic parent Hamiltonian of range at least one more than this length has
a positive gap uniform over all chain lengths. No normalization or pairwise
inequivalence assumptions are imposed on the original blocks.

This combines the block-injective interaction range in CPGSV21,
arXiv:2011.12127, Section IV.C, lines 2114--2129, with its gap theorem,
lines 2183--2187. The finite-range periodic comparison is documented in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`.

**Scope restriction (simultaneous injectivity range):**
`exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_wordTupleSpanTop`
proves the gap only at ranges \(R\geq S+1\), for a supplied \(S>0\) at which the
length-\(S\) word tuples of the blocks span the full product matrix algebra
(lines 2114--2129). The gap theorem at lines 2183--2187 is stated for all parent
Hamiltonians without a range hypothesis. Documented in
`docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex`.
-/

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

/-- Simultaneous injectivity at length \(S\) gives a uniform periodic gap at
every range at least \(S + 1\), with no normalization hypotheses on the blocks.
Source: CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129 and 2183--2187. -/
theorem exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_wordTupleSpanTop
    {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S R : ℕ} (hS : 0 < S)
    (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ) [NeZero N], ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R N).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, _⟩ :=
    exists_hasComplementaryFixedPointGap_family_of_wordTupleSpanTop A hS hSpan
  have hKernel : ∀ W, R ≤ W →
      LinearMap.ker
          (Matrix.toEuclideanLin
              (parentChainInteraction (toTensorFromBlocks (d := d) (μ := μ) B) R W).hamiltonian) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) B) W :=
    fun W hRW ↦ ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_groundSpaceES
      μ B hμ (fun j ↦ (hP j).norm)
      (fun n hn ↦ wordTupleSpanTop_of_ge_of_tracePreserving B hSpanB
        (fun j ↦ (hP j).norm) hn) hR hRW
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_ker_eq
      μ B hμ ρ hP hρ (fun i j hij h ↦ by
        simpa only [eqRec_eq_cast] using
          not_gaugePhaseEquiv_of_wordTupleSpanTop B hSpanB i j hij h) (by omega) hKernel
  refine ⟨γ, hγ, fun N _ ↦ ?_⟩
  rw [hamiltonian_parentRingInteraction_toTensorFromBlocks_eq_of_block_groundSpace_eq
    μ μ A B hμ hμ (fun j ↦ hGS j R) N]
  exact hGap N

end MPSTensor
