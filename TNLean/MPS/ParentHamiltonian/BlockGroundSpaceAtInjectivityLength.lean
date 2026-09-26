/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockWordSpanNormalization
import TNLean.MPS.ParentHamiltonian.BlockPeriodicClosure
import QICLean.Analysis.WeightedPositiveKernel

/-!
# Periodic ground spaces at the simultaneous injectivity length

Suppose the block words span the full product matrix algebra at a positive
length \(S\). For every interaction range \(S+1\leq L\leq N\), the periodic
local constraints have ground space equal to the span of the component MPS
vectors. In particular, the result includes the minimal ring \(N=S+1\).

This is the block-injective closure statement of CPGSV21,
arXiv:2011.12127, Section IV.C, lines 2114--2129. Its interaction range is
specified by the preceding intersection argument, lines 2044--2094; the
simultaneous injectivity length need not equal an individual block's C1 length.
-/

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
    exists_isPrimitiveMPS_family_parentHamiltonian_eq_of_wordTupleSpanTop
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
    (hker : ∀ i, LinearMap.ker (H i) =
      LinearMap.ker (localTermES (toTensorFromBlocks (d := d) (μ := μ) A) L i)) :
    LinearMap.ker (∑ i, H i) = (bntMPSVectorSpan A N).map
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap := by
  have hEq : LinearMap.ker (∑ i, H i) = LinearMap.ker
      (parentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ) A) L N) := by
    rw [parentHamiltonianES_eq_sum_localTermES,
      WeightedPositiveKernel.ker_sum_eq_iInf hH,
      WeightedPositiveKernel.ker_sum_eq_iInf (fun i ↦ localTermES_isPositive _ L i)]
    simp only [hker]
  rw [hEq, ← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_toTensorFromBlocks_eq_of_wordTupleSpanTop μ A hμ hS hSpan hSL hLN]

end MPSTensor
