# Issue #990 blocked-word comparison audit

## Scope

Issue #990 asks for the comparison between the weighted direct sum obtained by
blocking each original nonzero block at the common length $p$ and the weighted
direct sum obtained by the iterated-blocking relabelling used in
`CommonBlockedCyclicSectorFamily.commonReindexedBlock`.

The reusable finite-sum comparison theorem is recorded in
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

The same comparison gives one-sided zero-tail statements in
`TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean`:

- `zeroTail_commonFlat_of_blockwise`
- `zeroTail_commonFlat_of_word_eq`

These rewrite the zero-tail equation with the derived common-sector family from a
blockwise comparison, or directly from equality of the blocked words.

## Remaining point

The remaining theorem is now the pure blocked-word coordinate statement: for each
common cyclic-sector family `F`, block `k`, and physical index
`i : Fin (blockPhysDim d F.p)`, prove that the length-$p$ word decoded directly
from `i` is the same word as the length `F.period k * F.extra k` word obtained by
viewing `i` as an iterated block through `F.blockPhysDim_nested_eq k` and applying
`iteratedBlockIndex`.

Equivalently, the final comparison may be formulated with this relabelling of
blocked words explicit. No new mathematical assumptions about MPS tensors are
introduced here; the remaining question is the identification of the chosen
coordinates for direct and iterated blocked words. Since the current blocked
physical index is chosen through `Fintype.equivFin`, cardinal equality alone does
not specify how a length-`p` direct word is grouped into an iterated
`(m_k,e_k)` word; that coordinate choice has to be proved for the chosen
encoding or carried as an explicit relabelling.

## Paper path

This is exactly the bookkeeping step between the common-length cyclic-sector data
used after the period-removal construction and the common-sector block family used
by the later sector comparison theorems. It is independent of the Gemma/arXiv:1708
periodic fundamental theorem route and of parent-Hamiltonian arguments.
