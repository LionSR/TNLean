# Issue #934 — product-word span from BNT selector words (2026-04-26)

## Scope

Wave 16 Slot B targeted the Route B finite product-word span input for the parent-Hamiltonian
block decomposition.  The full paper-level theorem

```lean
IsCanonicalFormBNT μ A → ∃ m > 0, WordTupleSpanTop A m
```

is not yet proved from BNT separation alone.  This pass instead lands the next checked step on the
paper path: once the finite BNT selector-word theorem is available, canonical-form injectivity turns
those selectors into the required positive-length product-word span and into the downstream
projection/commutant input.

## Lean declarations added

File: `TNLean/MPS/CanonicalForm/BlockDiagonalCommutant.lean`

- `MPSTensor.isNBlkInjective_one_of_isInjective`
  - Records that one-site injectivity is `1`-block injectivity.
  - This supplies the prefix length used when concatenating block-spanning words with selector
    words.

- `MPSTensor.blockProjection_mem_span_reindexed_toTensorFromBlocks_of_wordTupleSpanTop`
  - `WordTupleSpanTop` spelling of the existing raw product-span projection theorem.

- `MPSTensor.wordTupleSpanTop_of_isCanonicalFormBNT_of_blockSelectorWords`
  - If `A` is in canonical form with BNT separation and `HasBlockSelectorWords A S`, then
    `WordTupleSpanTop A (1 + S)`.
  - Proof: use one-site injectivity for each block, then apply the existing
    `wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords` theorem from the MPDO finite
    witness infrastructure.

- `MPSTensor.exists_pos_productWordSpan_of_isCanonicalFormBNT_of_blockSelectorWords`
  - The issue-#934 goal shape with the selector-word theorem kept explicit:
    `∃ m, 0 < m ∧` the simultaneous length-`m` word tuples span the full product algebra.

- `MPSTensor.blockProjection_mem_span_reindexed_toTensorFromBlocks_of_bntSelectorWords`
  - Composes the preceding product-word span with the projection-span reduction for
    `toTensorFromBlocks μ A`.

- `MPSTensor.isBlockDiagonal'_of_commutes_reindexed_toTensorFromBlocks_of_bntSelectorWords`
  - Selector-word version of the assembled-tensor commutant criterion.

Blueprint Chapter 14 now records these declarations in
`lem:product_word_span_from_bnt_selectors` and updates the not-ready parent-ground-space theorem to
cite this selector-word reduction.

## Remaining blocker

The remaining mathematical content is still the finite BNT selector-word theorem:
from separated CF/BNT data (`blocks_not_equiv` together with injectivity and left-canonical
normalization), construct `HasBlockSelectorWords A S` for some finite `S`, or equivalently prove
finite matrix-entry word-family linear independence.  The likely route remains the one recorded in
issue #587/#822 notes: matrix-inserted word states, cross-sector Gram decay from BNT separation,
nondegenerate same-sector Gram limits, and then the Gram-matrix linear-independence criterion.

## Validation

Successful local checks in `wave16-B-934-product-word-span`:

- `lake env lean TNLean/MPS/CanonicalForm/BlockDiagonalCommutant.lean`
- `lake build TNLean.MPS.CanonicalForm.BlockDiagonalCommutant`
- `lake build TNLean.MPS.CanonicalForm.BlockDiagonalCommutant TNLean.MPS.MPDO.BiCFDerivation`
  `TNLean.MPS.BNT.Construction`
- `ulimit -n 8192 && lake build TNLean`
  - The first two full-build invocations reached the command timeout while continuing the local
    build; the final invocation completed successfully, with only pre-existing warnings in unrelated
    modules.
- `cd blueprint && leanblueprint web`
- `cd blueprint && leanblueprint checkdecls`
