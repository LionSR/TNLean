# Issue #942/#652 Wave 18 Slot A — per-block cyclic live data audit

Date: 2026-04-27
Branch/worktree: `wave18-A-942-common-live`

## Checked Lean progress

This branch advances the common-live-block predecessor without pretending that the
common physical flattening is already formalized.

1. `MPSTensor.HasPrimitiveIrreducibleCyclicSectors` in
   `TNLean/MPS/CanonicalForm/Assembly/CyclicSectorDecomposition.lean` packages the
   one-block period-removal output: for a tensor `A`, there is a positive
   period-removal length `m` such that `blockTensor A m` is represented by
   unit-weight sector blocks which are trace-preserving, have primitive transfer
   maps, are tensor-irreducible, and have positive bond dimensions.

2. `MPSTensor.hasPrimitiveIrreducibleCyclicSectors_of_TP_of_isIrreducibleTensor`
   repackages the existing checked cyclic-sector theorem
   `exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor`
   through that predicate.

3. `MPSTensor.tp_primitive_irreducible_extra_blocking` in
   `TNLean/MPS/CanonicalForm/Assembly/PrimitiveBlocks.lean` records the separate
   later-blocking step: if a sector block is already TP, primitive, and
   tensor-irreducible, then any positive extra blocking length `k` preserves TP,
   primitive transfer, and tensor irreducibility.  This is intentionally separate
   from the period-removal length `m`.

4. `MPSTensor.fundamentalTheorem_after_blocking_1606_perBlock_cyclic_live_with_zeroTail`
   in `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean` is the main
   predecessor theorem.  From `SameMPV₂ A B`, it:
   - applies the arbitrary-input zero-tail / TP-gauge reduction to both sides;
   - keeps the irreducible TP live blocks, nonzero weights, positive dimensions,
     and exact zero-tail MPV equations;
   - proves the two live tensors agree at all positive lengths, with the exact
     `N = 0` zero-tail bookkeeping identity retained; and
   - proves every live block on both sides has primitive irreducible cyclic
     sectors via the new predicate.

Blueprint entries were added for the checked declarations in
`blueprint/src/chapter/ch08_canonical.tex`:

- `def:primitive_irreducible_cyclic_sectors`, source quote:
  “some positive period-removal length $m$ represents $A^{[m]}$ as a unit-weight
  block tensor whose sector blocks are trace-preserving, have primitive transfer
  maps, are tensor-irreducible, and have positive bond dimensions.”
- `thm:has_primitive_irreducible_cyclic_sectors_tp_irr`, source quote:
  “Every trace-preserving irreducible tensor satisfies
  Definition~\ref{def:primitive_irreducible_cyclic_sectors}.”
- `thm:tp_primitive_irreducible_extra_blocking`, source quote:
  “This $k$ is the subsequent common-refinement or injectivity length, distinct
  from the period-removal length that produced the sector block.”
- `thm:ft_after_blocking_per_block_cyclic_live_zero_tail`, source quote:
  “The period-removal length for those sectors is kept separate from any later
  common blocking or injectivity length.”

## Paper-faithful route now represented

The checked theorem follows the intended canonical-form sequence:

1. invariant-subspace / zero-tail split;
2. TP gauge on the irreducible live blocks;
3. period removal by cyclic sectors for each live block; and only then
4. a later finite blocking length for common refinement or injectivity, when such
   a length is actually needed.

In particular, it does not reuse the earlier `exists_tp_primitive_blockDecomp_after_blocking`
output as if its blocked live blocks were automatically tensor-irreducible.  That
would conflate the period-removal blocking with the live sector blocks: an
irreducible periodic block can become reducible when blocked by its period, and
its primitive irreducible pieces are the cyclic sectors.

## Remaining blocker for the exact common-live theorem

The exact #942 target still needs a dependent-index flattening theorem:
starting from the per-live-block cyclic sector data, choose a common physical
blocking level `p`, express each sector at that level by an additional positive
blocking length `k`, transport through the nested-block physical-index equivalence
between `blockPhysDim (blockPhysDim d m) k` and `blockPhysDim d (m * k)`, flatten
`(live block, cyclic sector)` into one finite index family, and prove the exact
MPV identity for `blockTensor A p` and `blockTensor B p`.

That missing step is a real formal interface issue: it is about nested blocking
associativity, physical-index transport, and dependent finite-index regrouping.
It is not an overlap-span hypothesis and should not be hidden by assuming an
already-common primitive-irreducible live family.  Once this flattening is
available, the new extra-blocking lemma supplies the TP/primitive/irreducible
transport for the later common-refinement or injectivity length without confusing
that length with the period-removal period.
