/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockWordSpanSeparation
import TNLean.MPS.ParentHamiltonian.BlockWordSpanNormalization
import TNLean.MPS.ParentHamiltonian.BlockWordSpanPropagation
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockGap
import TNLean.MPS.ParentHamiltonian.Martingale.FixedRangeGapTransfer

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
-/

open Filter
open scoped Topology

namespace MPSTensor

/-- Simultaneous injectivity at length \(S\) gives a uniform periodic gap at
every range at least \(S + 1\), with no normalization hypotheses on the blocks.
Source: CPGSV21, arXiv:2011.12127, Section IV.C, lines 2114--2129 and 2183--2187. -/
theorem exists_parentHamiltonianES_toTensorFromBlocks_uniform_gap_of_wordTupleSpanTop
    {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S R : ℕ} (hS : 0 < S)
    (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, ∀ v ∈
      (LinearMap.ker (parentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ) A) R N))ᗮ,
      γ * ‖v‖ ≤ ‖parentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ) A) R N v‖ := by
  obtain ⟨B, ρ, hP, hρ, hSpanB, hGS, _⟩ :=
    exists_isPrimitiveMPS_family_of_wordTupleSpanTop A hS hSpan
  have hEq : ∀ N, parentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ) A) R N =
      parentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ) B) R N :=
    fun N ↦ parentHamiltonianES_toTensorFromBlocks_eq_of_block_groundSpace_eq
      μ μ A B hμ hμ (fun j ↦ hGS j R) N
  have hKernel : ∀ W, R ≤ W →
      LinearMap.ker (openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ) B) R W) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) B) W :=
    fun W hRW ↦ ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES
      μ B hμ (fun j ↦ (hP j).norm)
      (fun n hn ↦ wordTupleSpanTop_of_ge_of_tracePreserving B hSpanB
        (fun j ↦ (hP j).norm) hn) hR hRW
  simp_rw [hEq]
  obtain ⟨W, hRW, _, γ, hγ, hGap⟩ :=
    exists_ge_parentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS
      μ B hμ ρ hP hρ (fun i j hij h ↦ by
        simpa only [eqRec_eq_cast] using
          not_gaugePhaseEquiv_of_wordTupleSpanTop B hSpanB i j hij h) (2 * R)
  obtain ⟨δ, hδ, hPeriodic⟩ := exists_parentHamiltonianES_gap_of_larger_range
    (toTensorFromBlocks (d := d) (μ := μ) B) (by omega) hRW
    (hKernel W (by omega)) hγ hGap
  obtain ⟨M, hM⟩ := hPeriodic.exists_forall_of_atTop
  exact parentHamiltonianES_gap_of_eventual_gap
    (toTensorFromBlocks (d := d) (μ := μ) B) R M hδ hM

end MPSTensor
