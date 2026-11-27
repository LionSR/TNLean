/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Chain.Defs
import TNLean.MPS.Tensor.Physical.Blocking
import QICLean.Kraus.Transfer

/-!
# Blocking a site-dependent chain

A chain of `n` site-dependent tensors `A₀, …, A_{n-1}` with a common bond dimension `D` blocks
into one tensor on the alphabet `Fin n → Fin d`: its matrix at the word `σ` is the ordered
product `eval A σ = A₀^{σ₀} ⋯ A_{n-1}^{σ_{n-1}}`. For a constant chain this is the blocked
tensor `Kraus.block A n`.

The inhomogeneous matrix product states of arXiv:2307.01696, paragraph "Inhomogeneous
short-range correlated MPS", have "bond dimension at most `D`" varying along the ring; padding
their rectangular matrices with zeros (`VaryingBondChain.zeroPad`) gives a chain
with the common bond dimension `D` and the same state, to which the blocking here applies.

## Main declarations

* `MPSChainTensor.eval_const_eq_block` — for a constant chain the blocked tensor `eval A` is
  `Kraus.block A n`.
* `MPSChainTensor.eval_eq_prod_ofFn` — the ordered product along a chain as a list product.
* `MPSChainTensor.prod_transferMap_apply`, `MPSChainTensor.transferMap_eval`: ordered
  transfer products of inhomogeneous chains.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
-/

section BlockTensor

open scoped Matrix

namespace MPSChainTensor

variable {d D n : ℕ}

/-- The ordered product along a chain is the product of the list of its selected matrices. -/
theorem eval_eq_prod_ofFn (A : MPSChainTensor d D n) (σ : Fin n → Fin d) :
    eval A σ = (List.ofFn fun k => A k (σ k)).prod := by
  induction n with
  | zero => simp
  | succ n ih => rw [eval_succ, ih, List.ofFn_succ, List.prod_cons]

/-- On a constant chain, the ordered product is the evaluation of the word. -/
theorem eval_const (A : MPSTensor d D) (σ : Fin n → Fin d) :
    eval (fun _ => A) σ = Kraus.evalWord A (List.ofFn σ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [eval_succ, ih, List.ofFn_succ, Kraus.evalWord_cons]

/-- **The blocked tensor of a site-dependent chain.** Read as a family indexed by the words
`σ : Fin n → Fin d`, the ordered product `eval A` is the blocked tensor of the chain; for a
constant chain it is `Kraus.block A n`.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": the tensor obtained
"after blocking `q`" sites of a matrix product state that is not translation invariant. -/
theorem eval_const_eq_block (A : MPSTensor d D) :
    eval (fun _ : Fin n => A) = Kraus.block A n :=
  funext (eval_const A)

end MPSChainTensor

end BlockTensor

section Transfer

/-!
## Ordered transfer products of inhomogeneous chains

The transfer map of a blocked site-dependent chain is the ordered composition of its site
transfer maps, in the same order as the matrices in the physical coefficients. This identifies
an actual blocked tensor with the map used in uniform mixing estimates; powers of one map
are not substituted for products of different maps.

### Main results

* `MPSChainTensor.prod_transferMap_apply`: expansion in physical words.
* `MPSChainTensor.transferMap_eval`: the exact ordered transfer product.

### References

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
theorem transferMap_eval (A : MPSChainTensor d D n) :
    Kraus.transferMap (eval A) = (List.ofFn fun i => Kraus.transferMap (A i)).prod := by
  ext X : 1
  rw [prod_transferMap_apply, Kraus.transferMap_apply]

end MPSChainTensor

end Transfer
