/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalBoundaryClosing
import TNLean.MPS.ParentHamiltonian.BlockOpenGroundSpace
import TNLean.MPS.ParentHamiltonian.CyclicBoundaryIntertwining
import TNLean.MPS.ParentHamiltonian.BlockWordSpanPropagation
import TNLean.MPS.MPDO.SourceBNTBlocking

/-!
# Periodic closure from simultaneous block injectivity

A simultaneous word span at length \(S>0\) identifies the periodic ground space
at every interaction range \(L\geq S+1\) and chain length \(N\geq L\). Boundary
matrices at adjacent cyclic cuts intertwine with each one-site tensor. After
one circuit, these matrices commute with all length-\(N\) words and are scalar
within each block.

This is the block-diagonal closure argument in arXiv:2011.12127, Section IV.C,
lines 2126--2129, using the full-ring closure alternative at lines 2078--2079.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Simultaneous injectivity on the complementary \(N-1\) sites closes a family
of open-boundary representations at every cyclic cut. This is the cyclic
closure step of arXiv:2011.12127, Section IV.C, lines 2126--2129. -/
theorem mem_bntMPSVectorSpan_of_cyclic_openBoundary
    (A : (j : Fin r) → MPSTensor d (dim j)) {N : ℕ} (hN : 2 ≤ N)
    (hSpan : WordTupleSpanTop A (N - 1)) (ψ : NSiteSpace d N)
    (hBoundary : ∀ i : Fin N,
      ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        cyclicTranslateState i ψ = ∑ j, groundSpaceMap (A j) N (X j)) :
    ψ ∈ bntMPSVectorSpan A N := by
  classical
  let : NeZero N := ⟨by omega⟩
  choose X hX using hBoundary
  let s : Fin N := ⟨N - 1, by omega⟩
  have hStep : ∀ (i : Fin N) (a : Fin d) (j : Fin r),
      X i j * A j a = A j a * X (s + i) j := by
    intro i a j
    have h := block_boundary_intertwines_of_cyclicTranslate_sum_groundSpaceMap_eq_of_add_eq
      A (by omega : N - 1 + 1 = N) (by omega : 0 < 1) hSpan (X i) (X (s + i))
      (by rw [← hX i, ← hX (s + i), cyclicTranslateState_add]) (fun _ ↦ a) j
    simpa using h
  have hzero : ψ = ∑ j, groundSpaceMap (A j) N (X 0 j) := by
    rw [← hX 0]
    ext σ
    change ψ σ = ψ (cyclicTranslateCfg 0 σ)
    congr 1
    funext k
    simp [cyclicTranslateCfg]
  rw [hzero, ← iSup_mpvSubmodule_eq_bntMPSVectorSpan]
  refine Submodule.sum_mem _ fun j _ ↦ Submodule.mem_iSup_of_mem j ?_
  apply groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_long_word_commutes
    (isNBlkInjective_of_wordTupleSpanTop A hSpan j) (by omega : 0 < N - 1)
    (by omega : N - 1 ≤ N)
  intro ω
  exact boundary_commutes_evalWord_of_cyclic_intertwining
    (A j) (fun i ↦ X i j) s (fun i a ↦ hStep i a j) ω 0

/-- The periodic parent kernel is the span of the block MPS vectors once the
interaction range exceeds a simultaneous injectivity length. Trace-preserving
normalization supplies the open-chain intersection property. This is the
normalized form of arXiv:2011.12127, Section IV.C, lines 2126--2129. -/
theorem ker_parentHamiltonian_toTensorFromBlocks_eq_of_wordTupleSpanTop_of_tracePreserving
    [NeZero d] (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hTP : ∀ j, ∑ a, (A j a)ᴴ * A j a = 1)
    {S L N : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S)
    (hSL : S + 1 ≤ L) (hLN : L ≤ N) :
    LinearMap.ker
        (parentHamiltonian (toTensorFromBlocks (d := d) (μ := μ) A) L N) =
      bntMPSVectorSpan A N := by
  have hSpans : ∀ n ≥ S, WordTupleSpanTop A n := fun n hn ↦
    wordTupleSpanTop_of_ge_of_tracePreserving A hSpan hTP hn
  have hOpen : chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
      groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) N := by
    intro φ hφ
    apply contiguous_mem_groundSpace_toTensorFromBlocks μ A hμ hTP hSpans hSL hLN
    intro k hk τ
    rw [chainGroundSpace, dite_eq_left ⟨by omega, hLN⟩] at hφ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ
    rw [← cyclicRestrictₗ_eq_contiguousRestrictₗ (by omega : 0 < N) hLN
      (show (⟨k, by omega⟩ : Fin N).val + L ≤ N from hk)]
    exact hφ ⟨k, by omega⟩ τ
  refine le_antisymm ?_
    (bntMPSVectorSpan_le_ker_parentHamiltonian_toTensorFromBlocks μ A hμ (by omega) hLN)
  intro ψ hψ
  apply mem_bntMPSVectorSpan_of_cyclic_openBoundary A (by omega)
    (hSpans (N - 1) (by omega)) ψ
  intro i
  have hcyclic := cyclicTranslateState_mem_chainGroundSpace
    (toTensorFromBlocks (d := d) (μ := μ) A) (by omega) hLN i
    (ker_parentHamiltonian_le_chainGroundSpace _ (by omega) hLN hψ)
  obtain ⟨X, hX⟩ := hOpen hcyclic
  refine ⟨fun j ↦ (μ j) ^ N • Matrix.finSigmaDiagonalBlock X j, ?_⟩
  rw [← hX]
  exact BlockSumGroundSpace.groundSpaceMap_toTensorFromBlocks_eq_sum_diagonalBlock μ A N X

end MPSTensor
