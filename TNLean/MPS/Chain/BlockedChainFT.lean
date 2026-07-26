/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Chain.FundamentalTheorem

/-!
# Fundamental theorem for blocked chains

For an MPS tensor `A` and blocking length `L`, the constant blocked chain of
`A^{[L]}` satisfies the chain fundamental theorem with respect to the blocked
combined tensor.  The theorem hypothesis uses `SameMPV` on the combined
blocked tensors.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964)
-/

namespace MPSChainTensor

variable {d D : ℕ}

/-- Constant blocked chain obtained by repeating `blockTensor A L` at every site. -/
noncomputable def blockedChain (A : MPSTensor d D) (L n : ℕ) :
    MPSChainTensor (MPSTensor.blockPhysDim d L) D n :=
  fun _ => MPSTensor.blockTensor A L

/-- If `A` is `L`-block injective, then the constant chain of `L`-blocked tensors
is injective at every site. -/
lemma blockedChain_isInjective (A : MPSTensor d D) (L n : ℕ)
    (hA : MPSTensor.IsNBlkInjective A L) :
    IsInjective (blockedChain A L n) := by
  intro k
  simpa [blockedChain] using
    (MPSTensor.isNBlkInjective_iff_blockTensor_isInjective A L).1 hA

/-- **Fundamental Theorem for blocked chains**.

If the bond dimension and chain length are positive, `A` is `L`-block injective, and the
constant blocked chains built from
`A^{[L]}` and `B^{[L]}` satisfy `SameMPV` on their combined tensors, then
the blocked chains are gauge equivalent. -/
theorem fundamentalTheorem_blockedChain
    (A B : MPSTensor d D) (L n : ℕ)
    (hn : 0 < n) (hD : 0 < D)
    (hA_block : MPSTensor.IsNBlkInjective A L)
    (hMPV : MPSTensor.SameMPV
      (MPSTensor.chainCombinedTensor (blockedChain A L n))
      (MPSTensor.chainCombinedTensor (blockedChain B L n))) :
    GaugeEquiv (blockedChain A L n) (blockedChain B L n) :=
  fundamentalTheorem_injective_chain
    (blockedChain A L n)
    (blockedChain B L n)
    hn hD
    (blockedChain_isInjective A L n hA_block)
    hMPV

end MPSChainTensor
