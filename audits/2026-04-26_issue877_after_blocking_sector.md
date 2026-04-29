# Issue #877 Wave 16 Slot D — after-blocking sector composition audit

Date: 2026-04-26
Branch/worktree: `wave16-D-877-after-blocking-sector`

## Lean progress landed

The new #877 comparison layer does not introduce a `SectorBasisMatching` assumption for the
comparison step. Instead it adds three kernel-checked compositions.

1. `MPSTensor.SectorBasisOverlapSpanHypotheses` in
   `TNLean/MPS/FundamentalTheorem/SectorDecomposition.lean` bundles exactly the
   primitive overlap-rigidity inputs consumed by
   `exists_sectorBasisMatching_of_overlapOrtho_span_sameMPV`:
   - nonzero bond dimensions for both bases;
   - injectivity of all basis blocks;
   - left-canonical normalization;
   - self-overlap limits equal to `1` and off-overlap limits equal to `0`;
   - equality of the finite-length MPV spans.

   Its theorem
   `MPSTensor.SectorBasisOverlapSpanHypotheses.exists_sectorBasisMatching`
   converts those analytic inputs plus `SameMPV₂ P.toTensor Q.toTensor` into
   `Nonempty (SectorBasisMatching P Q)` by applying the #860 overlap-rigidity
   theorem. The permutation, dimension transport, gauge-phase data, and copy
   alignment are outputs, not assumptions.

2. `MPSTensor.fundamentalTheorem_after_blocking_1606_sector_of_bntPair_overlapSpan`
   in `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean` replaces the
   old abstract `matchedBasisData` argument with a BNT sector pair carrying
   `SectorBasisOverlapSpanHypotheses P Q`. It derives
   `SameMPV₂ P.toTensor Q.toTensor` from the original
   `hSame : SameMPV₂ A B`, constructs the matching witness through #860, and
   then applies
   `fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching` to
   obtain the actual sector-weight multiset conclusion.

3. `MPSTensor.fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_overlapSpan`
   additionally invokes the #923 one-sided constructor
   `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` on both sides. Its inputs
   are a common blocking period with exact live decompositions of
   `blockTensor A p` and `blockTensor B p` by TP primitive irreducible blocks
   with nonzero weights, plus a proof that the collapsed BNT bases satisfy
   `SectorBasisOverlapSpanHypotheses`. From these inputs and `SameMPV₂ A B`, it
   produces the same matched sector-weight conclusion as the issue target.

## Remaining blocker for the fully unconditional theorem

The requested hSame-only theorem

```lean
theorem fundamentalTheorem_after_blocking_1606_sector
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) : ...
```

still requires derivations that are not exposed by the current structural
reduction:

1. **Live common-block input.**
   `exists_tp_primitive_blockDecomp_after_blocking` returns a zero-tail term plus
   TP primitive blocks, but it does not return primitive-and-irreducible live
   blocks at a common physical blocking level in the exact form required by
   `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`. The cyclic-sector
   development proves primitive irreducible sector blocks, but the
   flattening/common-period construction from the zero-tail reduction to a single
   exact nonzero-block family is not yet a public theorem.

2. **Zero-tail bookkeeping at `N = 0`.**
   The sector comparison theorems use `SameMPV₂`, which includes length `N = 0`.
   The structural reduction expresses the blocked tensor as
   `zeroMPSTensor zeroTailDim + livePart`. Removing the zero tail gives equality
   of live parts for positive lengths immediately, but full `SameMPV₂` of the
   live sector tensors requires either equal zero-tail dimensions or a
   positive-length variant of the sector comparison/extrapolation layer.

3. **Live-block span comparison for the chosen sector bases.**
   PR #955 exposed the one-sided representative data needed by
   `SectorBasisOverlapSpanHypotheses`: positive dimensions, injectivity (from an
   explicit live-block injectivity input), normalization, and self/off-overlap
   limits. Wave 18B adds the missing quotient-span bookkeeping:
   `MPSTensor.MPVPhaseClassData.representative_mpv_span_eq` proves that the
   chosen MPV phase-class representatives span exactly the same finite-length MPV
   subspace as the original nonzero blocks, and
   `MPSTensor.exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq`
   transports an equality of the two original live-block spans to the two chosen
   sector bases. Thus the remaining span input is now precisely the nonzero-block
   span equality itself, not an opaque `SectorBasisOverlapSpanHypotheses` field.

## Wave 17 Slot G update

`MPSTensor.exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho`
strengthened the #923 constructor for the fields that are one-sided in nature:
positive basis dimensions, left-canonical normalization, self-overlap limits,
off-overlap limits, and representative injectivity when the original nonzero blocks
are one-site injective. The helper
`MPSTensor.SectorBasisOverlapOrthoHypotheses.to_overlapSpan` then combines those
one-sided fields with the two genuinely two-family inputs needed by the #860
overlap-rigidity theorem: injectivity of the chosen bases and equality of the
finite-length MPV spans.

## Wave 18B update

`MPSTensor.fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_blockSpan`
now replaces the two-sector span input by equality of the finite-length MPV spans
of the original nonzero-block families. The one-sided representative-span identity
transports those nonzero-block spans to the chosen BNT sector bases, and the #860
matching theorem then gives the sector-weight conclusion.

Therefore the available #923/#944/#955 and #860 ingredients now reduce the
unconditional theorem to the genuine structural inputs still missing from the
paper-level reduction: exact common nonzero-block decompositions, the `N = 0` zero-tail
identity, nonzero-block injectivity or a blocked replacement for the primitive
rigidity theorem, and finite-length span equality for the original nonzero-block
families from the global equal-MPV hypothesis.

## Issue #970 predecessor update

Issue #969 is not yet available on `origin/main`, so the final theorem deriving
nonzero-block finite-length span equality from the full structural `SameMPV₂` data
cannot honestly be proved in this step.  The new predecessor isolates a reusable
span mechanism for the common-block route:

- `MPSTensor.MPVBlockPhaseEquiv` records heterogeneous MPV phase equivalence
  between individual blocks, allowing different bond dimensions.
- `MPSTensor.mpv_span_eq_of_common_phase_cover` proves that if both nonzero-block
  families map surjectively to one common family and each nonzero block is
  MPV-phase equivalent to its image, then their finite-length MPV spans agree at
  every system size.
- `MPSTensor.fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_phaseCover`
  feeds this span equality directly into
  `fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_blockSpan`, so
  the exact-live sector comparison no longer needs a raw span-equality
  hypothesis once a future common-blocking theorem supplies the common family and
  the two surjective class maps.

This keeps the remaining #970 obligation mathematically honest: the unproved
paper-level input is now the construction of the common live family (with the
phase-cover maps) from the after-blocking structural reduction, together with
zero-tail and injectivity bookkeeping, rather than any further quotient/span
transport for the BNT representatives.
