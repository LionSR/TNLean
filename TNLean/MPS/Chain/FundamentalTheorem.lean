import TNLean.MPS.Chain.AlgebraIsomorphism
import TNLean.MPS.FundamentalTheorem.Basic

/-!
# Fundamental Theorem for injective MPS chains

Two injective MPS chains `A` and `B` whose combined tensors
`chainCombinedTensor A` and `chainCombinedTensor B` generate the same MPV
family are related by cyclic gauge transformations on the virtual bonds.

The hypothesis `SameMPV (chainCombinedTensor A) (chainCombinedTensor B)` is
trace agreement for all mixed-site words of all lengths.  The paper bridges
the gap from fixed-length `SameState` to this hypothesis via a blocking
argument for `n ≥ 3`; this bridging step is not formalized here.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Theorem 1
-/

open scoped Matrix

namespace MPSChainTensor

variable {d D n : ℕ}

/-- **Combined-tensor form of the injective chain Fundamental Theorem**
(Theorem 1 of arXiv:1804.04964).

If `A` and `B` are `n`-site chains with `A` injective and
`SameMPV (chainCombinedTensor A) (chainCombinedTensor B)`, then `A` and `B`
are cyclically gauge equivalent. The hypothesis is stated for the combined
tensors, whose physical index is the pair `(k, i)`. The proof produces a uniform gauge
(the same `X ∈ GL(D, ℂ)` at every bond), which is a special case of cyclic
gauge equivalence. -/
theorem fundamentalTheorem_injective_chain
    (A B : MPSChainTensor d D n)
    (hA : IsInjective A)
    (hMPV : MPSTensor.SameMPV (MPSTensor.chainCombinedTensor A)
      (MPSTensor.chainCombinedTensor B)) :
    GaugeEquiv A B := by
  /- Note: this formulation only assumes injectivity of `A`. The proof applies
  the single-block theorem to `chainCombinedTensor A`; no separate injectivity
  hypothesis on `B` is required. -/
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
