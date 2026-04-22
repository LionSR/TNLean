# Issue #609 blocker refresh — full-cycle contraction is still missing, now identifiable as a concrete `SameStateBridge` gap

## Scope

Target:
- `repeatedBlocks_of_blockedSectorGaugePhase` in `TNLean/MPS/Periodic/Overlap.lean`

Worktree / branch used for this retry:
- `.worktrees/issue-609`
- `feat/609-tier-a-repeatedBlocks`

Per protocol, before attempting proof code I:
- read the current issue #609 thread and posted the required short scout comment
- re-read the target theorem and surrounding private bridge lemmas in `TNLean/MPS/Periodic/Overlap.lean`
- re-read `TNLean/MPS/Chain/OneSidedInverse.lean`, `TNLean/MPS/Chain/TensorEquality.lean`, `TNLean/MPS/Chain/FundamentalTheorem.lean`, `TNLean/MPS/Chain/SameStateBridge.lean`, `TNLean/MPS/Chain/BlockedChainFT.lean`
- re-read the relevant contraction paper segment `Papers/1708.00029/main.tex` around Eqs. A.14–A.18
- checked existing blocker history (`audits/2026-04-21_issue608_609_bridge_blocker.md`, PR #733 docstring update)

## What I confirmed this session

### 1. The theorem-local blocker is still real on current `main`

The source-level note added in PR #733 is still accurate at a high level: the remaining missing ingredient is the paper's full-cycle `Ω_u` contraction / phase telescope, not the older Eq. A.8 transport gap.

Concretely, the target theorem already assumes the per-sector blocked gauge data

```lean
hBlockMatch : ∀ u, ∃ hdim, GaugePhaseEquiv ... (blocksA u) (blocksB (u + q))
```

so the missing step is the upgrade from those **sectorwise blocked** gauges to one **global per-site** `RepeatedBlocks A B` witness.

### 2. The newer chain infrastructure does **not** discharge this automatically

At first glance, the post-#8 chain API looks promising:

- `TNLean/MPS/Chain/FundamentalTheorem.lean`
  provides
  `MPSChainTensor.fundamentalTheorem_injective_chain`
  from
  `SameMPV (chainCombinedTensor A) (chainCombinedTensor B)`
  to cyclic chain gauge equivalence.
- `TNLean/MPS/Chain/BlockedChainFT.lean`
  packages the injective blocked-chain endpoint.

However, both stop exactly where the periodic Case-3 proof still gets stuck:

- `TNLean/MPS/Chain/SameStateBridge.lean` introduces only the **abstract interface**

```lean
structure SameStateBridgeHyp (d D : ℕ) : Prop where
  sameMPV_of_sameState :
    ∀ ⦃n : ℕ⦄ (A B : MPSChainTensor d D n),
      IsInjective A →
      3 ≤ n →
      SameState A B →
      MPSTensor.SameMPV (MPSTensor.chainCombinedTensor A)
        (MPSTensor.chainCombinedTensor B)
```

- There is **no concrete theorem on `main`** implementing this bridge.

So the chain library already packages the *endpoint* the paper wants, but not the
actual proof of the fixed-length-to-all-length upgrade. In Appendix A terms, the
missing proof is still the `Ω_u` contraction around Eqs. A.14–A.18.

### 3. Why this matters specifically for `repeatedBlocks_of_blockedSectorGaugePhase`

The paper's route is:

1. choose a common repetition length from `hNormal`
2. build injective repeated blocked tensors `F_u`
3. prove a fixed-length cyclic-chain equality (`SameState`) for the full `m`-cycle
4. contract with the `Ω_u` right inverses to obtain per-site tensor-product equality
5. telescope the sector phases to one global gauge / phase

On current `main`, steps (4)–(5) are not packaged anywhere.

I checked whether the existing chain route could replace them:

- `fundamentalTheorem_injective_chain` needs `SameMPV`, not just fixed-length `SameState`
- `fundamentalTheorem_injective_chain_of_sameState` in `SameStateBridge.lean` is only a wrapper around the **hypothetical** bridge object `SameStateBridgeHyp`
- `tensor_proportional` in `TNLean/MPS/Chain/TensorEquality.lean` is still only the **2-site** proportionality theorem and does not supply the full `m`-cycle bridge

So the present library contains the ingredients *around* the target step, but not the target step itself.

## Precise missing statement family

The smallest reusable theorem family I now see is:

### Reusable version (best location: `TNLean/MPS/Chain/SameStateBridge.lean`)

Replace the abstract bridge hypothesis by an actual theorem:

```lean
theorem sameMPV_of_sameState
    {d D n : ℕ}
    (A B : MPSChainTensor d D n)
    (hA : IsInjective A)
    (hn : 3 ≤ n)
    (hState : SameState A B) :
    MPSTensor.SameMPV (MPSTensor.chainCombinedTensor A)
      (MPSTensor.chainCombinedTensor B)
```

This is exactly the currently-abstract field of `SameStateBridgeHyp`.

### Local periodic specialization (minimal theorem that would unblock #609)

A theorem specialized to the injective repeated-block `m`-cycle built from the
sector data in Appendix A.14–A.18 would also suffice. Informally:

```lean
/-- Periodic `m`-cycle Ω-contraction / fixed-length-to-all-length bridge. -/
private theorem sameMPV_chainCombined_of_repeated_cycle
    (... periodic sector-chain data ...)
    (hInjectiveSites : ...)
    (hCycleState : MPSChainTensor.SameState cycleA cycleB) :
    MPSTensor.SameMPV
      (MPSTensor.chainCombinedTensor cycleA)
      (MPSTensor.chainCombinedTensor cycleB)
```

combined with `MPSChainTensor.fundamentalTheorem_injective_chain`.

Either formulation packages the same mathematical content: the full-cycle
`Ω_u` contraction that upgrades a fixed equality of the `m`-cycle to the all-word
compatibility needed for cyclic gauge extraction.

## Bottom line

I do **not** see an honest way to discharge
`repeatedBlocks_of_blockedSectorGaugePhase` inside its current file-local scope
on top of `main`.

The new refinement over the older #733 note is:

- the missing ingredient is not just "some m-factor analogue of `tensor_proportional`"
- it can be identified more concretely as the still-unimplemented **concrete theorem behind `SameStateBridgeHyp`**, or a periodic specialization of it

Until that bridge exists, the target theorem remains blocked.

## Files inspected this retry

- `TNLean/MPS/Periodic/Overlap.lean`
- `TNLean/MPS/Chain/OneSidedInverse.lean`
- `TNLean/MPS/Chain/TensorEquality.lean`
- `TNLean/MPS/Chain/FundamentalTheorem.lean`
- `TNLean/MPS/Chain/SameStateBridge.lean`
- `TNLean/MPS/Chain/BlockedChainFT.lean`
- `TNLean/MPS/ParentHamiltonian/BlockStrip.lean`
- `Papers/1708.00029/main.tex`

No Lean proof code is committed in this branch at the time of writing this note.
