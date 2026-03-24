import TNLean.MPS.Chain.FundamentalTheorem

/-!
# SameState-to-SameMPV bridge interface for chains

This module records the paper-facing blocking bridge as an explicit hypothesis:
from injectivity of `A`, a fixed-length equality `SameState A B` at some
`n ≥ 3`, and the blocking argument, obtain `SameMPV` for the combined tensors.

We keep this as a structure rather than a typeclass so downstream theorems can
choose the bridge argument explicitly at call sites without global instance
search.
-/

namespace MPSChainTensor

variable {d D n : ℕ}

/-- Abstract hypothesis encapsulating the missing blocking argument from
`SameState` (at some chain length `n ≥ 3`) to `SameMPV` on combined tensors.

The injectivity precondition on `A` matches the paper-facing route used by the
chain fundamental theorem endpoint. -/
structure SameStateBridgeHyp (A B : MPSChainTensor d D n) : Prop where
  n_ge_three : 3 ≤ n
  bridge :
    IsInjective A →
    SameState A B →
    MPSTensor.SameMPV (MPSTensor.chainCombinedTensor A)
      (MPSTensor.chainCombinedTensor B)

/-- Bridge lemma: from the abstract blocking hypothesis and fixed-length
`SameState`, obtain `SameMPV` for the combined tensors. -/
theorem sameMPV_chainCombined_of_sameState
    (A B : MPSChainTensor d D n)
    (hBridge : SameStateBridgeHyp A B)
    (hA : IsInjective A)
    (hState : SameState A B) :
    MPSTensor.SameMPV (MPSTensor.chainCombinedTensor A)
      (MPSTensor.chainCombinedTensor B) :=
  hBridge.bridge hA hState

/-- Paper-style endpoint: `SameState` plus the bridge hypothesis implies the
usual chain fundamental-theorem conclusion `GaugeEquiv`. -/
theorem fundamentalTheorem_injective_chain_of_sameState
    (A B : MPSChainTensor d D n)
    (hBridge : SameStateBridgeHyp A B)
    (hA : IsInjective A)
    (hState : SameState A B) :
    GaugeEquiv A B :=
  fundamentalTheorem_injective_chain A B hA
    (sameMPV_chainCombined_of_sameState A B hBridge hA hState)

end MPSChainTensor
