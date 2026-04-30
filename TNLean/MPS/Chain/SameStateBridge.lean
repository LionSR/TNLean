import TNLean.MPS.Chain.FundamentalTheorem

/-!
# SameState to SameMPV bridge interface for injective chains

The paper's blocking argument (for chain length `n ≥ 3`) upgrades a fixed-length
`SameState` hypothesis to the all-length mixed-word trace agreement `SameMPV`
needed by `fundamentalTheorem_injective_chain`.

This file encodes that blocking step as an explicit hypothesis object and
provides convenience lemmas/theorems that consume it.
-/


namespace MPSChainTensor

variable {d D n : ℕ}

/-- Abstract hypothesis for the paper's blocking step:

If `A` is injective and two chains agree at fixed length `n ≥ 3` (`SameState`),
then their combined tensors satisfy `SameMPV`. -/
/- Design note: this is a `structure` (rather than a `class`) so callers pass
   this bridge assumption explicitly instead of relying on instance search. -/
structure SameStateBridgeHyp (d D : ℕ) : Prop where
  sameMPV_of_sameState :
    ∀ ⦃n : ℕ⦄ (A B : MPSChainTensor d D n),
      IsInjective A →
      3 ≤ n →
      SameState A B →
      MPSTensor.SameMPV (MPSTensor.chainCombinedTensor A)
        (MPSTensor.chainCombinedTensor B)

/-- Bridge lemma interface:
from fixed-length `SameState` (`n ≥ 3`) and injectivity of `A`, obtain `SameMPV`
for combined tensors using a supplied blocking hypothesis. -/
theorem sameMPV_chainCombined_of_sameState
    (hBridge : SameStateBridgeHyp d D)
    (A B : MPSChainTensor d D n)
    (hA : IsInjective A)
    (hn : 3 ≤ n)
    (hState : SameState A B) :
    MPSTensor.SameMPV (MPSTensor.chainCombinedTensor A)
      (MPSTensor.chainCombinedTensor B) :=
  hBridge.sameMPV_of_sameState A B hA hn hState

/-- Paper-style chain theorem:
assuming the blocking bridge hypothesis, fixed-length `SameState` at `n ≥ 3`
implies cyclic gauge equivalence for injective `A`. -/
theorem fundamentalTheorem_injective_chain_of_sameState
    (hBridge : SameStateBridgeHyp d D)
    (A B : MPSChainTensor d D n)
    (hA : IsInjective A)
    (hn : 3 ≤ n)
    (hState : SameState A B) :
    GaugeEquiv A B :=
  fundamentalTheorem_injective_chain A B hA
    (sameMPV_chainCombined_of_sameState hBridge A B hA hn hState)

end MPSChainTensor
