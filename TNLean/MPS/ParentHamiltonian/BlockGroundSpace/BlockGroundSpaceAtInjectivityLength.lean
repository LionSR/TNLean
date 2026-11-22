/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.GroundSpace.BoundaryOverlap
import Mathlib.GroupTheory.OrderOfElement
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BoundaryMatrix.BNTBlockDiagonalBoundaryClosing
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockOpenGroundSpace
import TNLean.MPS.CanonicalForm.BlockSeparation.BlockWordSpanPropagation
import TNLean.MPS.CanonicalForm.BlockSeparation.SimultaneousBlocking
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockWordSpanNormalization
import QICLean.Spectral.Gap.WeightedPositiveKernel

/-!
# Cyclic propagation of boundary intertwiners

A boundary matrix which intertwines adjacent cyclic cuts commutes with every
word extending once around the cycle. This is the algebraic propagation step
of the periodic closure argument in the proof of Theorem 10 ("Uniqueness
with TI and PBC") of PGVWC07, arXiv:quant-ph/0608197, lines 1272--1289. The
proof of Theorem 12 invokes the same argument for several blocks (lines 1454--1455).

## Periodic closure from simultaneous block injectivity

A simultaneous word span at length \(S>0\) identifies the periodic ground space
at every interaction range \(L\geq S+1\) and chain length \(N\geq L\). Boundary
matrices at adjacent cyclic cuts intertwine with each one-site tensor. After
one circuit, these matrices commute with all length-\(N\) words and are scalar
within each block.

This is the block-diagonal closure argument in arXiv:2011.12127, Section IV.C,
lines 2126--2129, using the full-ring closure alternative at lines 2078--2079.

## Periodic ground spaces at the simultaneous injectivity length

Suppose the block words span the full product matrix algebra at a positive
length \(S\). For every interaction range \(S+1\leq L\leq N\), the periodic
local constraints have ground space equal to the span of the component MPS
vectors. In particular, the result includes the minimal ring \(N=S+1\).

This is the block-injective closure statement of CPGSV21,
arXiv:2011.12127, Section IV.C, lines 2114--2129. Its interaction range is
specified by the preceding intersection argument, lines 2044--2094; the
simultaneous injectivity length need not equal an individual block's C1 length.
-/

section

namespace MPSTensor

/-- Propagating adjacent boundary intertwiners around one full cycle gives
commutation with every matrix word of that length. -/
theorem boundary_commutes_evalWord_of_cyclic_intertwining
    {d D N : ℕ} [NeZero N] (A : MPSTensor d D)
    (Y : Fin N → Matrix (Fin D) (Fin D) ℂ) (s : Fin N)
    (hStep : ∀ i a, Y i * A a = A a * Y (s + i))
    (ω : Fin N → Fin d) (i : Fin N) :
    Y i * Kraus.evalWord A (List.ofFn ω) =
      Kraus.evalWord A (List.ofFn ω) * Y i := by
  have hcycle : N • s = 0 := by simpa using (card_nsmul_eq_zero (x := s))
  have hpath := boundary_witness_product_of_adjacent_overlaps
    (A := A) (fun r : Fin (N + 1) ↦ Y (r.val • s + i)) ω ω
    (fun r : Fin N ↦ by
      simpa [succ_nsmul, add_assoc, add_comm, add_left_comm] using
        hStep (r.val • s + i) (ω r))
  simpa [hcycle] using hpath

end MPSTensor

end

section

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

end

section

open scoped BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- The periodic local constraints have exactly the span of the component
MPS vectors as their ground space once the interaction range exceeds the
supplied simultaneous injectivity length. Source: CPGSV21,
arXiv:2011.12127, Section IV.C, lines 2126--2129. The interaction range on
\(S+1\) sites is that of the normal-tensor theorem at lines 2087--2094; the
closure argument at lines 2078--2079 allows larger interactions. -/
theorem chainGroundSpace_toTensorFromBlocks_eq_of_wordTupleSpanTop
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S L N : ℕ}
    (hS : 0 < S) (hSpan : WordTupleSpanTop A S)
    (hSL : S + 1 ≤ L) (hLN : L ≤ N) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
      bntMPSVectorSpan A N := by
  obtain ⟨B, ρ, hP, _hρ, hSpanB, hHam, hBNT⟩ :=
    exists_hasComplementaryFixedPointGap_family_parentHamiltonian_eq_of_wordTupleSpanTop
      μ A hμ hS hSpan
  rw [← ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) hLN, hHam, hBNT]
  exact ker_parentHamiltonian_toTensorFromBlocks_eq_of_wordTupleSpanTop_of_tracePreserving
    μ B hμ (fun j ↦ (hP j).norm) hS hSpanB hSL hLN

/-- The canonical periodic parent Hamiltonian has precisely the component
MPS span as its kernel, including at the minimal ring length \(S+1\).
Source: CPGSV21, arXiv:2011.12127, Section IV.C, lines 2126--2129. -/
theorem ker_parentHamiltonian_toTensorFromBlocks_eq_of_wordTupleSpanTop
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S L N : ℕ}
    (hS : 0 < S) (hSpan : WordTupleSpanTop A S)
    (hSL : S + 1 ≤ L) (hLN : L ≤ N) :
    LinearMap.ker (parentHamiltonian (toTensorFromBlocks (d := d) (μ := μ) A) L N) =
      bntMPSVectorSpan A N := by
  rw [ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) hLN]
  exact chainGroundSpace_toTensorFromBlocks_eq_of_wordTupleSpanTop μ A hμ hS hSpan hSL hLN

/-- Any positive local terms with the prescribed parent kernels have the
same periodic ground space. The terms need not be orthogonal projections.
Source: CPGSV21, arXiv:2011.12127, the parent-Hamiltonian definition at
lines 1995--2007 and the block-injective conclusion at lines 2126--2129. -/
theorem ker_sum_eq_bntMPSVectorSpan_of_wordTupleSpanTop
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S L N : ℕ}
    (hS : 0 < S) (hSpan : WordTupleSpanTop A S)
    (hSL : S + 1 ≤ L) (hLN : L ≤ N)
    (H : Fin N → EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N))
    (hH : ∀ i, (H i).IsPositive)
    (hker : haveI : NeZero N := ⟨by omega⟩; ∀ i, LinearMap.ker (H i) = LinearMap.ker
      (Matrix.toEuclideanLin ((parentRingInteraction (toTensorFromBlocks μ A) L N).term i))) :
    LinearMap.ker (∑ i, H i) = (bntMPSVectorSpan A N).map
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap := by
  have : NeZero N := ⟨by omega⟩
  have hEq : LinearMap.ker (∑ i, H i) = LinearMap.ker
      (Matrix.toEuclideanLin (parentRingInteraction (toTensorFromBlocks μ A) L N).hamiltonian) := by
    rw [ManyBody.Interaction.hamiltonian, map_sum, WeightedPositiveKernel.ker_sum_eq_iInf hH,
      WeightedPositiveKernel.ker_sum_eq_iInf (fun i ↦ Matrix.isPositive_toEuclideanLin_iff.mpr
        (posSemidef_parentRingInteraction_term _ _ i))]
    simp only [hker]
  rw [hEq, ← ManyBody.groundSpace_zero,
    groundSpace_hamiltonian_parentRingInteraction_eq_map_ker,
    ker_parentHamiltonian_toTensorFromBlocks_eq_of_wordTupleSpanTop μ A hμ hS hSpan hSL hLN]

end MPSTensor

end
