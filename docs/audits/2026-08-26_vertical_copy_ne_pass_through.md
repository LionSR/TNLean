# Unequal retained vertical-copy forwarder retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. The two declarations below were `private`
shadows of one shared theorem: each restated its signature verbatim and proved
it by `exact` on the shared owner, and each sat in a one-theorem namespace that
was immediately reopened with `open`, so the call sites in the same file read
identically before and after the removal.

| Removed | Replacement |
|---|---|
| `MPOTensor.VerticalCopyBlocks.verticalAssembledTensor_apply_copy_ne` (`TNLean/MPS/MPDO/VerticalCopyBlocks.lean`) | `MPOTensor.verticalAssembledTensor_apply_copy_ne` (`TNLean/MPS/MPDO/VerticalSectorCoordinates.lean`) |
| `MPOTensor.VerticalProductRetainedBlocks.verticalAssembledTensor_apply_copy_ne` (`TNLean/MPS/MPDO/VerticalProductRetainedBlocks.lean`) | `MPOTensor.verticalAssembledTensor_apply_copy_ne` (`TNLean/MPS/MPDO/VerticalSectorCoordinates.lean`) |

## What was checked

Both removed theorems carried the shared owner's exact signature and a
single-line proof delegating to it. Both files sit inside `namespace MPOTensor`
and import `TNLean.MPS.MPDO.VerticalSectorCoordinates` transitively, so the
three unqualified uses — one in `VerticalCopyBlocks.lean` and two in the
`rw [...]` steps of `VerticalProductRetainedBlocks.lean` — now resolve to
`MPOTensor.verticalAssembledTensor_apply_copy_ne` with no call-site edit.

Both removed declarations are `private`, so no external consumer is possible
and no blueprint `\lean{...}` tag can name them; no transition declaration is
warranted.

## Ledger

The entry "Unequal retained vertical-copy evaluation" in
`docs/tactic_patterns.md` recorded the two forwarders as delegating to the
shared owner. Its result bullet now records that the call sites invoke the
owner directly. The contrast it draws with
`MPOTensor.verticalAssembledTensor_apply_copy_same` is unchanged.
