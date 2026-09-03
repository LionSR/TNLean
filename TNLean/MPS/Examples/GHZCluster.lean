/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.BondReindex
import TNLean.MPS.Core.TensorProductSpan
import TNLean.MPS.Examples.Cluster
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.RFP.BNTOrthogonality

/-!
# The Z4 × Z2 GHZ-cluster tensor

This module constructs the tensor product of the GHZ tensor with the once-blocked
cluster tensor.  It has physical dimension eight and bond dimension four.  Its
two bond-dimension-two blocks are supported on disjoint values of the GHZ
physical qubit.

The construction formalizes arXiv:2502.20257, equation `eq:z4z2MPS`, the block
formulas on lines 4448--4479, and line 4481, first sentence. It stops before the
Z4 × Z2 actions, action tensors, L-symbols, block-independence classification,
fusion operators, and gauging.

## Main definitions

* `z4z2GHZClusterTensor` is the GHZ tensor product with the blocked cluster tensor.
* `z4z2GHZClusterBlock` is either one of its two injective blocks.
* `z4z2GHZClusterDirectSum` is their canonical block-diagonal direct sum.

## Main results

* `z4z2GHZClusterBlock_apply` is the formula
  $A^{(x),(p,q)} = \delta_{x,p} C^q$.
* `z4z2GHZClusterBlock_isInjective` proves injectivity of both blocks.
* `z4z2GHZClusterBlocks_isBNTLocallyOrthogonal` proves local orthogonality
  directly from disjoint GHZ support.
* `z4z2GHZClusterDirectSum_eq_tensor` identifies the direct sum with the source
  tensor.
-/

open scoped Matrix BigOperators Kronecker
open Matrix Finset

noncomputable section

namespace MPSTensor

/-- The Z4 × Z2 example tensor from arXiv:2502.20257, equation `eq:z4z2MPS`:
the GHZ tensor tensored with the once-blocked cluster tensor. -/
def z4z2GHZClusterTensor : MPSTensor 8 4 :=
  tensorProduct ghzTensor clusterBlocked

/-- The block labeled by the GHZ value `x`, on the full eight-dimensional
physical alphabet.  This is the product of the one-dimensional GHZ sector and
the blocked cluster tensor. -/
def z4z2GHZClusterBlock (x : Fin 2) : MPSTensor 8 2 :=
  tensorProduct (ghzSectorTensor x) clusterBlocked

private theorem finProdFinEquiv_zero_two (a : Fin 2) :
    finProdFinEquiv ((0 : Fin 1), a) = a := by
  rfl

/-- Exact block formula from arXiv:2502.20257, lines 4448--4479:
$A^{(x),(p,q)} = \delta_{x,p} C^q$. -/
@[simp] theorem z4z2GHZClusterBlock_apply (x p : Fin 2) (q : Fin 4) :
    z4z2GHZClusterBlock x (finProdFinEquiv (p, q)) =
      if p = x then clusterBlocked q else 0 := by
  ext a b
  have h := tensorProduct_apply (ghzSectorTensor x) clusterBlocked p q 0 0 a b
  rw [finProdFinEquiv_zero_two, finProdFinEquiv_zero_two] at h
  by_cases hpx : p = x <;>
    simpa [z4z2GHZClusterBlock, ghzSectorTensor, hpx] using h

/-- Each of the two GHZ-cluster blocks is injective.  This is the tensor-product
injectivity theorem applied to a one-dimensional GHZ sector and the existing
injective blocked cluster tensor. -/
theorem z4z2GHZClusterBlock_isInjective (x : Fin 2) :
    Kraus.IsInjective (z4z2GHZClusterBlock x) :=
  isInjective_tensorProduct _ _ (ghzSectorTensor_isInjective x)
    clusterBlocked_isInjective

/-- The two blocks are locally orthogonal because their GHZ physical supports
are disjoint.  The proof is the direct termwise mixed-map calculation described
at arXiv:2502.20257, line 4481, first sentence; it uses no
renormalization-group limit. -/
theorem z4z2GHZClusterBlocks_isBNTLocallyOrthogonal :
    IsBNTLocallyOrthogonal (dim := fun _ : Fin 2 => 2) z4z2GHZClusterBlock := by
  intro x y hxy
  ext X a b
  rw [Kraus.mixedMapLM_apply, Matrix.sum_apply]
  simp only [LinearMap.zero_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  obtain ⟨⟨p, q⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 4)).surjective i
  rw [z4z2GHZClusterBlock_apply, z4z2GHZClusterBlock_apply]
  by_cases hpx : p = x
  · subst p
    simp [hxy]
  · simp [hpx]

private theorem z4z2GHZCluster_totalDim :
    (∑ _ : Fin 2, 2) = 4 := by
  decide

/-- The canonical direct sum of the two GHZ-cluster blocks, using
`finSigmaFinEquiv` internally and then the canonical equality of its total bond
dimension with four. -/
def z4z2GHZClusterDirectSum : MPSTensor 8 4 :=
  reindex z4z2GHZCluster_totalDim
    (directSumTensor (dim := fun _ : Fin 2 => 2) z4z2GHZClusterBlock)

private theorem z4z2GHZCluster_bondCoordinate (x a : Fin 2) :
    finCongr z4z2GHZCluster_totalDim.symm (finProdFinEquiv (x, a)) =
      finSigmaFinEquiv ⟨x, a⟩ := by
  apply Fin.ext
  fin_cases x
  · simp [finSigmaFinEquiv_apply, finProdFinEquiv]
  · simp [finSigmaFinEquiv_apply, finProdFinEquiv]
    omega

private theorem z4z2GHZClusterTensor_apply (p x y : Fin 2) (q : Fin 4)
    (a b : Fin 2) :
    z4z2GHZClusterTensor (finProdFinEquiv (p, q))
        (finProdFinEquiv (x, a)) (finProdFinEquiv (y, b)) =
      if x = y then if p = x then clusterBlocked q a b else 0 else 0 := by
  rw [z4z2GHZClusterTensor, tensorProduct_apply]
  simp only [ghzTensor_apply, Matrix.diagonal_apply, Pi.single_apply]
  by_cases hxy : x = y
  · subst y
    simp [eq_comm]
  · simp [hxy]

private theorem z4z2GHZClusterDirectSum_apply (p x y : Fin 2) (q : Fin 4)
    (a b : Fin 2) :
    z4z2GHZClusterDirectSum (finProdFinEquiv (p, q))
        (finProdFinEquiv (x, a)) (finProdFinEquiv (y, b)) =
      if x = y then if p = x then clusterBlocked q a b else 0 else 0 := by
  rw [z4z2GHZClusterDirectSum, reindex_apply_apply,
    z4z2GHZCluster_bondCoordinate, z4z2GHZCluster_bondCoordinate]
  simp only [directSumTensor, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  by_cases hxy : x = y
  · subst y
    rw [Matrix.blockDiagonal'_apply_eq, z4z2GHZClusterBlock_apply]
    by_cases hpx : p = x <;> simp [hpx]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hxy]
    simp [hxy]

/-- The canonical direct sum of the two injective blocks is the GHZ tensor
product with the blocked cluster tensor.  The equality compares the
`finSigmaFinEquiv` direct-sum coordinates with the `finProdFinEquiv`
tensor-product coordinates from arXiv:2502.20257, equation `eq:z4z2MPS`
and lines 4448--4479. -/
theorem z4z2GHZClusterDirectSum_eq_tensor :
    z4z2GHZClusterDirectSum = z4z2GHZClusterTensor := by
  ext i c d
  obtain ⟨⟨p, q⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 4)).surjective i
  obtain ⟨⟨x, a⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective c
  obtain ⟨⟨y, b⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective d
  rw [z4z2GHZClusterDirectSum_apply, z4z2GHZClusterTensor_apply]

end MPSTensor
