import TNLean.MPS.Chain.FundamentalTheorem

/-!
# SameState → SameMPV bridge interface for injective chains

This file provides an API boundary for the blocking step used in
[arXiv:1804.04964](https://arxiv.org/abs/1804.04964):
for chains of length `n ≥ 3`, equality of the physical chain state (`SameState`)
should imply all-length mixed-word trace equality of the combined tensors
(`SameMPV` on `chainCombinedTensor`).

The full blocking proof is not formalized yet in this repository; instead,
we package it as a reusable hypothesis `SameStateBridgeHyp`. The theorem
`sameMPV_chainCombined_of_sameState` is the direct bridge lemma under that
hypothesis, and `fundamentalTheorem_injective_chain_of_sameState` is the
corresponding endpoint that feeds into the existing chain FT.
-/

open scoped Matrix

namespace MPSChainTensor

open MPSTensor

variable {d D n : ℕ}

/-- Abstract blocking bridge hypothesis for chains of fixed length `n`.

When `3 ≤ n`, chain-state equality at that length implies `SameMPV` for the
combined tensors. This matches the bridge step used between the paper's
`SameState` assumption and the repository's current `SameMPV`-based chain FT.
-/
def SameStateBridgeHyp (d D n : ℕ) : Prop :=
  ∀ (A B : MPSChainTensor d D n),
    3 ≤ n →
      SameState A B →
        SameMPV (chainCombinedTensor A) (chainCombinedTensor B)

/-- Bridge lemma: under `SameStateBridgeHyp`, `SameState` at length `n ≥ 3`
implies `SameMPV` for the combined tensors. -/
theorem sameMPV_chainCombined_of_sameState
    (hBridge : SameStateBridgeHyp d D n)
    (A B : MPSChainTensor d D n)
    (hn : 3 ≤ n)
    (hSame : SameState A B) :
    SameMPV (chainCombinedTensor A) (chainCombinedTensor B) :=
  hBridge A B hn hSame

/-- Chain FT endpoint using `SameState` plus the blocking bridge hypothesis.

This is a convenience wrapper around `fundamentalTheorem_injective_chain`.
It exposes the paper-style `SameState` input while keeping the current
`SameMPV`-based core theorem unchanged. -/
theorem fundamentalTheorem_injective_chain_of_sameState
    (hBridge : SameStateBridgeHyp d D n)
    (A B : MPSChainTensor d D n)
    (hn : 3 ≤ n)
    (hA : IsInjective A)
    (hSame : SameState A B) :
    GaugeEquiv A B := by
  apply fundamentalTheorem_injective_chain A B hA
  exact sameMPV_chainCombined_of_sameState hBridge A B hn hSame

end MPSChainTensor
