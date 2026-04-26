# Issue #877 Wave 16 Slot D — after-blocking sector assembly audit

Date: 2026-04-26
Branch/worktree: `wave16-D-877-after-blocking-sector`

## Lean progress landed

This branch does not introduce a `SectorBasisMatching` assumption for the #877 assembly step.  Instead it adds two kernel-checked wiring layers.

1. `MPSTensor.SectorBasisOverlapSpanHypotheses` in `TNLean/MPS/FundamentalTheorem/SectorDecomposition.lean` bundles exactly the primitive overlap-rigidity inputs consumed by `exists_sectorBasisMatching_of_overlapOrtho_span_sameMPV`:
   - nonzero bond dimensions for both bases;
   - injectivity of all basis blocks;
   - left-canonical normalization;
   - self-overlap limits equal to `1` and off-overlap limits equal to `0`;
   - equality of the finite-length MPV spans.

   Its theorem `MPSTensor.SectorBasisOverlapSpanHypotheses.exists_sectorBasisMatching` converts those analytic inputs plus `SameMPV₂ P.toTensor Q.toTensor` into `Nonempty (SectorBasisMatching P Q)` by applying the #860 overlap-rigidity theorem.  The permutation, dimension transport, gauge-phase data, and copy alignment are outputs, not assumptions.

2. `MPSTensor.fundamentalTheorem_after_blocking_1606_sector_of_bntPair_overlapSpan` in `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean` replaces the old abstract `matchedBasisData` argument with a BNT sector pair carrying `SectorBasisOverlapSpanHypotheses P Q`.  It derives `SameMPV₂ P.toTensor Q.toTensor` from the original `hSame : SameMPV₂ A B`, constructs the matching witness through #860, and then applies `fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching` to obtain the real sector-weight multiset conclusion.

3. `MPSTensor.fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_overlapSpan` additionally invokes the #923 one-sided constructor `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` on both sides.  Its inputs are a common blocking period with exact live decompositions of `blockTensor A p` and `blockTensor B p` by TP primitive irreducible blocks with nonzero weights, plus a proof that the collapsed BNT bases satisfy `SectorBasisOverlapSpanHypotheses`.  From these inputs and `SameMPV₂ A B`, it produces the same matched sector-weight endpoint as the issue target.

## Remaining blocker for the fully unconditional theorem

The requested hSame-only theorem

```lean
theorem fundamentalTheorem_after_blocking_1606_sector
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) : ...
```

still requires derivations that are not exposed by the current structural reduction:

1. **Live common-block input.**  `exists_tp_primitive_blockDecomp_after_blocking` returns a zero-tail term plus TP primitive blocks, but it does not return primitive-and-irreducible live blocks at a common physical blocking level in the exact form required by `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`.  The cyclic-sector development proves primitive irreducible sector blocks, but the flattening/common-period assembly from the zero-tail reduction to a single exact live block family is not yet a public theorem.

2. **Zero-tail bookkeeping at `N = 0`.**  The sector comparison theorems use `SameMPV₂`, which includes length `N = 0`.  The structural reduction expresses the blocked tensor as `zeroMPSTensor zeroTailDim + livePart`; removing the zero tail gives equality of live parts for positive lengths immediately, but full `SameMPV₂` of the live sector tensors requires either equal zero-tail dimensions or a positive-length variant of the sector comparison/extrapolation layer.

3. **Overlap/span hypotheses for the collapsed BNT bases.**  The one-sided #923 constructor proves `HasBNTSectorData` but does not expose injectivity, left-canonical normalization of the chosen representatives, asymptotic overlap orthogonality, or equality of the finite-length spans between the two sides.  These are exactly the fields of `SectorBasisOverlapSpanHypotheses`; deriving them from the collapsed representatives is the next paper-level task.

Therefore this branch wires the available #923 and #860 ingredients without hiding the missing work behind `SectorBasisMatching`.  The remaining work is to prove the listed live-block and overlap/span facts for the actual sector decompositions produced by the after-blocking reduction.
