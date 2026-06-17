# 2026-04-30 — Common primitive irreducible block decompositions (#942/#969/#990/#944/#652)

## Scope

This note records the Lean theorem added for issue #942.  It is a conditional
two-sided theorem: once the one-sided equality after reindexing blocked physical
words is available, the common cyclic-sector construction gives the two weighted
nonzero-sector families required before the injectivity and BNT comparison
arguments.

The theorem is deliberately not a full fundamental theorem.  It does not prove the
blocked-word reindexing equality tracked by #990, it does not add the later
Wielandt/injectivity blocking, and it does not construct the cross-side BNT
proportional-decomposition data.

## Source anchors

- `Papers/1606.00608/MPDO-22-12-17-2.tex:214--231` describes the reduction to
  a block-diagonal nonzero part and the subsequent common blocking by the
  periods; line 217 gives the weighted direct sum and lines 227--231 describe
  period removal by a common multiple.
- `Papers/2011.12127/TN-Review-main.tex:1798--1820` gives the corresponding
  irreducible trace-preserving block form and explains that blocking by the
  period makes the transfer operator primitive.
- `Papers/2011.12127/TN-Review-main.tex:1841--1884` introduces the basis of
  normal tensors and the coefficient expansions consumed by the BNT comparison
  stage.

## Lean statement

The new theorem is

```lean
MPSTensor.afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts
```

It assumes `SameMPV₂ A B` and the one-sided theorem asserting, for every
`CommonBlockedCyclicSectorFamily F`, that the canonically blocked weighted
nonzero part agrees as an MPV family with the same weighted family written using
`F.commonReindexedBlock`.  Under that assumption it produces:

- one common physical blocking length `p` with `0 < p`;
- zero-tail dimensions on the two sides;
- two weighted nonzero-sector families over `blockPhysDim d p`;
- zero-tail equations for `blockTensor A p` and `blockTensor B p` written with
  these weighted sector families;
- positive-length MPV equality between each blocked tensor and its nonzero
  sector part;
- positive-length MPV equality between the two nonzero sector parts;
- the length-zero zero-tail identity;
- nonzero weights;
- trace preservation, primitive transfer maps, tensor irreducibility, and
  positive bond dimensions for every sector block.

The proof composes
`fundamentalTheorem_after_blocking_commonLength_commonSector` with
`CommonBlockedCyclicSectorFamily.sameMPV₂_weightedCanonicalBlock_commonFlat_of_reindexed`.
The zero-tail equations and the positive-length equality are obtained by
substitution in the already formalized common-length zero-tail bookkeeping.

## Remaining hypotheses

The theorem leaves three mathematically distinct obligations.

1. **Agreement after reindexing blocked physical words.**  The needed one-sided
   statement is the #990 equality comparing the canonically blocked weighted
   nonzero part with the weighted `commonReindexedBlock` family.  Once this is
   proved, it can be passed directly as the `hReindexed` argument of the new
   theorem.
2. **Injectivity after a further blocking, or a replacement theorem.**  The new
   theorem gives trace preservation, primitive transfer maps, tensor irreducibility,
   nonzero weights, and positive bond dimensions.  The current overlap-span
   route to #944/#652 also assumes one-site injectivity of the final sector
   blocks.
3. **Common phase-cover or BNT proportional-decomposition data.**  The comparison
   theorems in Chapter 11 turn such data into finite-length nonzero-sector span
   equality and then into sector-weight comparison.  This branch supplies the
   common nonzero-sector decompositions to which those theorems apply after the
   preceding two obligations are supplied.
