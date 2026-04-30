# 2026-04-28 — Issue #969 common reblocking predecessor

## Scope

Issue #969 asks for the global construction that takes the per-block cyclic-sector data from
`MPSTensor.HasPrimitiveIrreducibleCyclicSectors` and expresses all resulting sectors at one
common physical blocking length.

This PR lands a checked predecessor for that step.

## Paper route checked

The implementation follows the period-removal route described in:

- `Papers/2011.12127/TN-Review-main.tex` lines 1774--1836: remove
  invariant-subspace redundancy, then block by the periods to obtain normal blocks.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 187--250: after irreducible
  block extraction, block by the least common multiple of the periodicities.

The new statements keep the period-removal lengths distinct from any later common refinement
or injectivity/Wielandt blocking length.

## Lean declarations added

- `MPSTensor.blockPhysDim_blockPhysDim`: physical dimension of iterated blocking agrees
  with one-step blocking by the product length.
- `MPSTensor.sameMPV₂_blockTensor_blockTensor_mul_reindex`: iterated blocking and
  one-step blocking have the same MPV family after the physical labels are identified by
  flattening iterated blocks.
- Physical-dimension transport lemmas in `TNLean/MPS/Core/BlockingInfrastructure.lean`
  for `SameMPV₂`, `toTensorFromBlocks`, trace preservation, transfer-map primitivity,
  and tensor irreducibility.
- `MPSTensor.CommonBlockedCyclicSectorFamily`: one-sided data structure for a finite
  nonzero-weight block family. It stores:
  - a single positive blocking length `p`;
  - per-block period-removal lengths `period k`;
  - later positive reblocking lengths `extra k` with `p = period k * extra k`;
  - the original cyclic sector blocks;
  - a flattened finite sector family at physical dimension `blockPhysDim d p`;
  - TP, primitive transfer maps, tensor irreducibility, positive dimensions;
  - the checked per-block iterated-blocking MPV compatibility condition.
- `MPSTensor.CommonBlockedCyclicSectorFamily.flatWeight` and `.flatWeight_ne_zero`:
  the flattened common-reblocked sectors carry nonzero unit weights.
- `MPSTensor.exists_commonBlockedCyclicSectorFamily_of_hasPrimitiveIrreducibleCyclicSectors`:
  constructs the one-sided common reblocked family by taking the LCM of the per-block
  periods and applying `tp_primitive_irreducible_extra_blocking` to each cyclic sector.
- `MPSTensor.fundamentalTheorem_after_blocking_commonBlocked_cyclic_live_with_zeroTail`:
  combines the zero-tail/TP-gauge reduction for nonzero-weight blocks with the one-sided
  common reblocking constructor on both sides, preserving positive-length nonzero-part
  equality and the exact `N = 0` zero-tail bookkeeping.

## What remains for full #969 closure

The new statements deliberately expose the remaining formal obligations:

1. Use the iterated-blocking relabeling theorem inside the common cyclic-sector data so
   each `(B_k^[period k])^[extra k]` is replaced by the corresponding one-step block
   `B_k^[p]` with the same flattened physical labels.
2. Flatten the weighted direct sum over original nonzero-weight blocks and cyclic sectors,
   transporting the original nonzero weights through the common blocking length.
3. Re-express the zero-tail equations after the common physical reblocking, including the
   exact length-zero bookkeeping.
4. Use the flattened common-alphabet nonzero-weight block family as the exact nonzero-part
   datum for the sector comparison theorem from PR #960 once the finite-length span equality
   is available.

This is therefore progress on #969/#942/#652, but not the final exact common nonzero-block
decomposition of `blockTensor A p` and `blockTensor B p`.
