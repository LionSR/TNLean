import TNLean.MPS.Chain.AlgebraIsomorphism
import TNLean.MPS.FundamentalTheorem.Basic

/-!
# Fundamental Theorem for injective MPS chains

This file proves the Fundamental Theorem for non-translation-invariant injective
MPS chains (Theorem 1 of [arXiv:1804.04964](https://arxiv.org/abs/1804.04964)):

Two injective MPS chains whose combined tensors generate the same MPV family are
related by cyclic gauge transformations on the virtual bonds.

## Proof strategy

We pack all site-local tensors into a single combined tensor via
`chainCombinedTensor`, then apply the single-block Fundamental Theorem
(`fundamentalTheorem_singleBlock`) to obtain a uniform gauge. A uniform gauge
is a special case of cyclic gauge equivalence.

## Hypothesis

The hypothesis `SameMPV (chainCombinedTensor A) (chainCombinedTensor B)` asks
for trace agreement of all mixed-site words of all lengths. This is stronger
than the paper's `SameState` (trace agreement at a single chain length). The
paper bridges this gap via a blocking argument requiring n ≥ 3; that bridging
step is not formalized here, so the theorem is stated with the stronger
hypothesis.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Theorem 1
-/

open scoped Matrix

namespace MPSChainTensor

variable {d D n : ℕ}

/-- **Fundamental Theorem for injective MPS chains** (Theorem 1, arXiv:1804.04964).

Two injective MPS chains whose combined tensors generate the same MPV family
are related by cyclic gauge transformations on the virtual bonds. The proof
produces a *uniform* gauge (the same invertible matrix at every bond), which is
stronger than the general cyclic gauge equivalence.

The hypothesis is `SameMPV` on the combined tensor (all-length trace agreement
for mixed-site words), which is stronger than the paper's fixed-length
`SameState`. See the module docstring for discussion. -/
theorem fundamentalTheorem_injective_chain
    (A B : MPSChainTensor d D n)
    (hA : IsInjective A)
    (hMPV : MPSTensor.SameMPV (MPSTensor.chainCombinedTensor A)
      (MPSTensor.chainCombinedTensor B)) :
    GaugeEquiv A B := by
  rcases n with _ | n
  · -- n = 0: no sites, gauge equivalence is vacuously true.
    exact ⟨Fin.elim0, fun k => k.elim0⟩
  · -- n ≥ 1: the combined tensor inherits injectivity from site 0.
    have hCA : MPSTensor.IsInjective (MPSTensor.chainCombinedTensor A) :=
      MPSTensor.chainCombinedTensor_isInjective A ⟨0, Nat.succ_pos n⟩ (hA ⟨0, Nat.succ_pos n⟩)
    -- Apply the single-block fundamental theorem to the combined tensor.
    obtain ⟨X, hX⟩ := MPSTensor.fundamentalTheorem_singleBlock hCA hMPV
    -- The uniform gauge X at every bond gives cyclic gauge equivalence.
    exact ⟨fun _ => X, fun k i => by
      have := hX (finProdFinEquiv (k, i))
      simp only [MPSTensor.chainCombinedTensor_apply] at this
      exact this⟩

end MPSChainTensor
