# Issue #990 blocked-word comparison audit

## Scope

Issue #990 asks for the comparison between the weighted direct sum obtained by
blocking each original nonzero block at the common length $p$ and the weighted
direct sum obtained by the iterated-blocking relabelling used in
`CommonBlockedCyclicSectorFamily.commonReindexedBlock`.

The reusable finite-sum comparison theorems are recorded in
`TNLean/MPS/CanonicalForm/Assembly/CyclicSectorDecomposition.lean`:

- `CommonBlockedCyclicSectorFamily.blockTensor_eq_commonReindexedBlock_of_word_eq`
- `CommonBlockedCyclicSectorFamily.blockTensor_sameMPV₂_commonReindexedBlock_of_word_eq`
- `CommonBlockedCyclicSectorFamily.sameMPV₂_weightedCanonicalBlock_commonReindexedBlock_of_blockwise`
- `CommonBlockedCyclicSectorFamily.sameMPV₂_weightedCanonicalBlock_commonReindexedBlock_of_word_eq`
- `CommonBlockedCyclicSectorFamily.sameMPV₂_weightedCanonicalBlock_commonFlat_of_blockwise`
- `CommonBlockedCyclicSectorFamily.sameMPV₂_weightedCanonicalBlock_commonFlat_of_word_eq`

These show that once the direct length-$p$ blocked word is identified with the
flattened iterated $(m_k,e_k)$ blocked word for each original nonzero block, the
comparison automatically assembles over the weighted direct sum and composes with
the common cyclic-sector family.

The issue #1075 refinement adds a canonical grouping map in
`TNLean/MPS/Core/BlockingInfrastructure.lean`:

- `blockWordChunk`
- `directToIteratedBlockIndex`
- `flattenBlockedWord_wordOfBlock_directToIteratedBlockIndex`
- `wordOfBlock_iteratedBlockIndex_directToIteratedBlockIndex`

For a direct blocked index of length $m n$, this map decodes its word, cuts it
into $n$ consecutive words of length $m$, encodes those words as the letters of
an iterated block, and proves that flattening the resulting iterated index
recovers the original direct word.

The assembly file also records the exact remaining coordinate assertion as
`CommonBlockedCyclicSectorFamily.groupedBlockCastAgrees` and provides the
corresponding comparison theorems:

- `CommonBlockedCyclicSectorFamily.wordOfBlock_eq_iteratedBlockIndex_of_groupedBlockCastAgrees`
- `CommonBlockedCyclicSectorFamily.blockTensor_eq_commonReindexedBlock_of_groupedBlockCastAgrees`
- `CommonBlockedCyclicSectorFamily.blockTensor_sameMPV₂_commonReindexedBlock_of_groupedBlockCastAgrees`
- `CommonBlockedCyclicSectorFamily.sameMPV₂_weightedCanonicalBlock_commonReindexedBlock_of_groupedBlockCastAgrees`
- `CommonBlockedCyclicSectorFamily.sameMPV₂_weightedCanonicalBlock_commonFlat_of_groupedBlockCastAgrees`

The same comparison gives one-sided zero-tail statements in
`TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean`:

- `zeroTail_commonFlat_of_blockwise`
- `zeroTail_commonFlat_of_word_eq`
- `zeroTail_commonFlat_of_groupedBlockCastAgrees`

These rewrite the zero-tail equation with the derived common-sector family from a
blockwise comparison, directly from equality of the blocked words, or from the
sharpened coordinate assertion `groupedBlockCastAgrees`.

## Remaining point

The remaining theorem is now sharpened to a precise coordinate assertion.  For
each common cyclic-sector family `F`, block `k`, and physical index
`i : Fin (blockPhysDim d F.p)`, the numeric cast

```lean
Fin.cast ((F.blockPhysDim_nested_eq k).symm) i
```

must agree with the index obtained by first rewriting the direct alphabet to the
product length `F.period k * F.extra k` and then applying
`directToIteratedBlockIndex`.  This is the proposition
`F.groupedBlockCastAgrees k`.

The new core theorem proves that `directToIteratedBlockIndex` is the mathematically
expected grouping map: applying `iteratedBlockIndex` to it recovers the original
direct blocked word.  Thus no MPS-theoretic assumption remains hidden in the
comparison lemmas.  What remains is only the compatibility between this grouping
map and the particular numeric `Fin.cast` used by `CommonBlockedCyclicSectorFamily`.

Since the current blocked physical index is chosen through `Fintype.equivFin`,
cardinal equality alone does not specify that the numeric order on the two `Fin`
types is the consecutive grouping order.  That coordinate choice must either be
proved for the chosen enumeration or kept as the explicit relabelling recorded by
`groupedBlockCastAgrees`.

## Paper path

This is exactly the bookkeeping step between the common-length cyclic-sector data
used after the period-removal construction and the common-sector block family used
by the later sector comparison theorems. It is independent of the Gemma/arXiv:1708
periodic fundamental theorem route and of parent-Hamiltonian arguments.
