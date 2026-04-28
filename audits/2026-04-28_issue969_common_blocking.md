# 2026-04-28 — Issue #969 common reblocking predecessor

## Scope

Issue #969 asks for the global assembly step that takes the per-live-block cyclic-sector data from `MPSTensor.HasPrimitiveIrreducibleCyclicSectors` and expresses all resulting sectors at one common physical blocking length.

This PR lands a checked predecessor for that step.

## Paper route checked

The implementation follows the period-removal route described in:

- `Papers/2011.12127/TN-Review-main.tex` lines 1774--1836: remove invariant-subspace redundancy, then block by the periods to obtain normal blocks.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 187--250: after irreducible block extraction, block by the least common multiple of the periodicities.

The new statements keep the period-removal lengths distinct from any later common refinement or injectivity/Wielandt blocking length.

## Lean declarations added

- `MPSTensor.blockPhysDim_blockPhysDim`: physical dimension of iterated blocking agrees with one-shot blocking by the product length.
- Physical-dimension transport lemmas in `TNLean/MPS/Core/BlockingInfrastructure.lean` for `SameMPV₂`, `toTensorFromBlocks`, trace preservation, transfer-map primitivity, and tensor irreducibility.
- `MPSTensor.CommonBlockedCyclicSectorFamily`: one-sided data structure for a finite live-block family. It stores:
  - a single positive blocking length `p`;
  - per-block period-removal lengths `period k`;
  - later positive reblocking lengths `extra k` with `p = period k * extra k`;
  - the original cyclic sector blocks;
  - a flattened finite sector family at physical dimension `blockPhysDim d p`;
  - TP, primitive transfer maps, tensor irreducibility, positive dimensions;
  - the checked per-live-block iterated-blocking MPV compatibility condition.
- `MPSTensor.CommonBlockedCyclicSectorFamily.flatWeight` and `.flatWeight_ne_zero`: the flattened common-reblocked sectors carry nonzero unit weights.
- `MPSTensor.exists_commonBlockedCyclicSectorFamily_of_hasPrimitiveIrreducibleCyclicSectors`: constructs the one-sided common reblocked family by taking the LCM of the per-block periods and applying `tp_primitive_irreducible_extra_blocking` to each cyclic sector.
- `MPSTensor.fundamentalTheorem_after_blocking_1606_commonBlocked_cyclic_live_with_zeroTail`: combines the zero-tail/TP-gauge live-block reduction with the one-sided common reblocking constructor on both sides, preserving positive-length live equality and the exact `N = 0` zero-tail bookkeeping.

## What remains for full #969 closure

The new API deliberately exposes the remaining formal obligations instead of hiding them:

1. Prove a one-shot iterated-blocking MPV/tensor compatibility theorem identifying `(B_k^[period k])^[extra k]` with `B_k^[p]` at the MPV equivalence needed by `toTensorFromBlocks`.
2. Flatten the weighted direct sum over original live blocks and cyclic sectors, transporting the original nonzero weights through the common blocking length.
3. Re-express the zero-tail equations after the common physical reblocking, including the exact length-zero bookkeeping.
4. Use the flattened common-alphabet live block family as the exact-live input for the sector comparison theorem from PR #960 once the finite-length span equality is available.

This is therefore strong progress on #969/#942/#652, but not the final exact-live common-block decomposition of `blockTensor A p` and `blockTensor B p`.
