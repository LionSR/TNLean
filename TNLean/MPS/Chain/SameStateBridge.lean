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

/-- Abstract hypothesis carrying the chain-length side condition (`n ≥ 3`) used
by the blocking step from `SameState` to `SameMPV`.

TODO: replace the `sorry` in `sameMPV_chainCombined_of_sameState` with a full
formalization of the blocking argument under this side condition. -/
structure SameStateBridgeHyp (A B : MPSChainTensor d D n) : Prop where
  n_ge_three : 3 ≤ n

/-- Bridge lemma (currently conditional): from fixed-length `SameState`,
injectivity, and `n ≥ 3`, derive `SameMPV` for the combined tensors.

TODO: this theorem is intentionally left as `sorry` until the blocking argument
is formalized in Lean. -/
theorem sameMPV_chainCombined_of_sameState
    (A B : MPSChainTensor d D n)
    (hBridge : SameStateBridgeHyp A B)
    (hA : IsInjective A)
    (hState : SameState A B) :
    MPSTensor.SameMPV (MPSTensor.chainCombinedTensor A)
      (MPSTensor.chainCombinedTensor B) := by
  have hn_ge_three : 3 ≤ n := hBridge.n_ge_three
  let _ := hn_ge_three
  let _ := hA
  let _ := hState
  sorry

/-- Paper-style endpoint: `SameState` plus the bridge hypothesis implies the
usual chain fundamental-theorem conclusion `GaugeEquiv`.

TODO: this endpoint remains conditional on the missing blocking argument used
in `sameMPV_chainCombined_of_sameState`. -/
theorem fundamentalTheorem_injective_chain_of_sameState
    (A B : MPSChainTensor d D n)
    (hBridge : SameStateBridgeHyp A B)
    (hA : IsInjective A)
    (hState : SameState A B) :
    GaugeEquiv A B :=
  fundamentalTheorem_injective_chain A B hA
    (sameMPV_chainCombined_of_sameState A B hBridge hA hState)

end MPSChainTensor
