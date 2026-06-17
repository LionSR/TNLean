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
- `blockIndexOfList_wordOfBlock`
- `flattenBlockedWord_wordOfBlock_directToIteratedBlockIndex`
- `wordOfBlock_iteratedBlockIndex_directToIteratedBlockIndex`

The issue #990 follow-up records this grouping map as a genuine equivalence:

- `wordOfBlock_injective`
- `iteratedBlockIndex_directToIteratedBlockIndex`
- `directToIteratedBlockIndex_surjective`
- `directToIteratedBlockIndex_iteratedBlockIndex`
- `directIteratedBlockEquiv`
- `eq_directToIteratedBlockIndex_iff_iteratedBlockIndex_eq`

For a direct blocked index of length $m n$, this map decodes its word, cuts it
into $n$ consecutive words of length $m$, encodes those words as the letters of
an iterated block, and proves that flattening and regrouping are inverse
operations on blocked indices, not only on decoded words.

The assembly file also records the exact remaining coordinate assertion as
`CommonBlockedCyclicSectorFamily.groupedBlockCastAgrees`, the equivalent
post-flattening formulation
`CommonBlockedCyclicSectorFamily.groupedBlockCastAgrees_iff_iteratedBlockIndex_cast`,
and the corresponding comparison theorems:

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

The remaining theorem is now sharpened to a precise coordinate assertion. For
each common cyclic-sector family `F`, block `k`, and physical index
`i : Fin (blockPhysDim d F.p)`, the canonical `Fin.cast` identification

```lean
Fin.cast ((F.blockPhysDim_nested_eq k).symm) i
```

must agree with the index obtained by first rewriting the direct alphabet to the
product length `F.period k * F.extra k` and then applying
`directToIteratedBlockIndex`. This is the proposition
`F.groupedBlockCastAgrees k`.

The core theorem now proves that `directToIteratedBlockIndex` is the
mathematically expected grouping map: together with `iteratedBlockIndex`, it is
an equivalence between direct length-$m n$ blocked indices and iterated
length-$n$ blocked indices whose letters are length-$m$ blocked words. The
assembly theorem
`CommonBlockedCyclicSectorFamily.groupedBlockCastAgrees_iff_iteratedBlockIndex_cast`
therefore narrows the remaining point to one assertion: after applying
`iteratedBlockIndex`, the canonical `Fin.cast` identification must give the same
direct blocked index as the length rewrite coming from
`F.p_eq_period_mul_extra k`.

Since the current blocked physical index is chosen through `Fintype.equivFin`,
cardinal equality alone does not specify that the order on the two `Fin` types
is the consecutive grouping order. That coordinate choice must either be proved
for the chosen enumeration or kept as the explicit relabelling recorded by
`groupedBlockCastAgrees`.

## Paper path

This is exactly the bookkeeping step between the common-length cyclic-sector data
used after the period-removal construction and the common-sector block family used
by the later sector comparison theorems. It is independent of the Gemma/arXiv:1708
periodic fundamental theorem route and of parent-Hamiltonian arguments.

## 2026-05-01: reindexPhysical lemma (wave 27)

Added `reindexPhysical_directToIteratedBlockIndex_blockTensor` in
`TNLean/MPS/Core/BlockingInfrastructure.lean`.  This lemma bypasses the
`Fin.cast` / `Fintype.equivFin` identification entirely and proves that the
explicit block-grouping bijection `directToIteratedBlockIndex`, applied to
the iterated block tensor via `reindexPhysical`, recovers the direct block
tensor at length $m \cdot n$.

The proof uses `blockTensor_blockTensor_eq_reindex` (already proved) and
`iteratedBlockIndex_directToIteratedBlockIndex` to cancel the forward and
inverse maps of the `directIteratedBlockEquiv`.

The remaining obstruction for #990 is now documented explicitly in the
source as a module doc comment (`### Blocked-word identification gap`):
one must prove that the `Fin.cast` identification used in
`CommonBlockedCyclicSectorFamily` coincides with `directToIteratedBlockIndex`.
This is a pure statement about `Fintype.equivFin` for function types,
independent of the MPS theory.
