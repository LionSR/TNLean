/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.BlockTensor
import QICLean.Kraus.Transfer

/-!
# Ordered transfer products of inhomogeneous chains

The transfer map of a blocked site-dependent chain is the ordered composition of its site
transfer maps, in the same order as the matrices in the physical coefficients. This identifies
an actual blocked tensor with the map used in uniform mixing estimates; powers of one map
are not substituted for products of different maps.

## Main results

* `MPSChainTensor.prod_transferMap_apply`: expansion in physical words.
* `MPSChainTensor.transferMap_blockTensor`: the exact ordered transfer product.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS" and eq. (8), which
  identifies the regrouped blocked Gram matrix with the transfer map.
-/

open Matrix
open scoped BigOperators

namespace MPSChainTensor

variable {d D n : ℕ}

/-- The ordered composition of site transfer maps sums over all words of the chain. -/
theorem prod_transferMap_apply (A : MPSChainTensor d D n) (X : Matrix (Fin D) (Fin D) ℂ) :
    ((List.ofFn fun i => Kraus.transferMap (A i)).prod) X =
      ∑ s, eval A s * X * (eval A s)ᴴ := by
  induction n with
  | zero => simp [Finset.univ_unique]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    change Kraus.transferMap (A 0)
      (((List.ofFn fun i => Kraus.transferMap (A i.succ)).prod) X) = _
    rw [ih]
    simp only [map_sum, Kraus.transferMap_apply]
    rw [Finset.sum_comm, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d)).sum_comp,
      Fintype.sum_prod_type]
    congr 1
    funext i
    apply Finset.sum_congr rfl
    intro s _
    simp [eval_succ, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Blocking an inhomogeneous chain composes its transfer maps in order.** This applies
also to a contiguous block extracted from a longer ring; the first site's map is the outermost
map in the composition. -/
theorem transferMap_blockTensor (A : MPSChainTensor d D n) :
    Kraus.transferMap (blockTensor A) = (List.ofFn fun i => Kraus.transferMap (A i)).prod := by
  classical
  ext X : 1
  rw [prod_transferMap_apply, Kraus.transferMap_apply]
  exact Fintype.sum_equiv (MPSTensor.decodeBlockEquiv d n)
    (fun t => blockTensor A t * X * (blockTensor A t)ᴴ)
    (fun s => eval A s * X * (eval A s)ᴴ) (fun _ => rfl)

end MPSChainTensor
