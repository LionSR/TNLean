/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.Defs
import TNLean.MPS.Core.Blocking

/-!
# Blocking a site-dependent chain

A chain of `n` site-dependent tensors `A₀, …, A_{n-1}` with a common bond dimension `D` blocks
into one tensor of physical dimension `d^n`: its matrix at the word `σ` is the ordered product
`A₀^{σ₀} ⋯ A_{n-1}^{σ_{n-1}}`. For a constant chain this is the blocked tensor
`MPSTensor.blockTensor A n`.

The inhomogeneous matrix product states of arXiv:2307.01696, paragraph "Inhomogeneous
short-range correlated MPS", have "bond dimension at most `D`" varying along the ring; padding
their rectangular matrices with zeros (`MPSPreparation.VaryingBondChain.zeroPad`) gives a chain
with the common bond dimension `D` and the same state, to which the blocking here applies.

## Main declarations

* `MPSChainTensor.blockTensor` — the blocked tensor of a site-dependent chain.
* `MPSChainTensor.blockTensor_const` — for a constant chain it is `MPSTensor.blockTensor`.
* `MPSChainTensor.eval_eq_prod_ofFn` — the ordered product along a chain as a list product.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
-/

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

/-- **The blocked tensor of a site-dependent chain.** Its matrix at the blocked index of the word
`σ` is the ordered product `A₀^{σ₀} ⋯ A_{n-1}^{σ_{n-1}}`.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": the tensor obtained
"after blocking `q`" sites of a matrix product state that is not translation invariant. -/
noncomputable def blockTensor (A : MPSChainTensor d D n) :
    MPSTensor (MPSTensor.blockPhysDim d n) D :=
  fun t => eval A (MPSTensor.decodeBlockEquiv d n t)

@[simp] theorem blockTensor_decodeBlockEquiv_symm (A : MPSChainTensor d D n)
    (σ : Fin n → Fin d) :
    blockTensor A ((MPSTensor.decodeBlockEquiv d n).symm σ) = eval A σ := by
  simp [blockTensor]

/-- The blocked tensor of a constant chain is the blocked tensor of its tensor. -/
theorem blockTensor_const (A : MPSTensor d D) :
    blockTensor (fun _ : Fin n => A) = MPSTensor.blockTensor A n := by
  funext t
  obtain ⟨σ, rfl⟩ := (MPSTensor.decodeBlockEquiv d n).symm.surjective t
  rw [blockTensor_decodeBlockEquiv_symm, eval_const]
  simp only [MPSTensor.blockTensor, MPSTensor.decodeBlockEquiv, Kraus.blockTensor,
    Kraus.wordOfBlock, Kraus.decodeBlock_decodeBlockEquiv_symm]

end MPSChainTensor
