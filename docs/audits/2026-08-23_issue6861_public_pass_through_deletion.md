# Issue #6861: public pass-through deletion audit

This batch removes public pass-through declarations whose names had no
non-Archive consumer, Blueprint citation, or documentation reference at the
branch point.  Some carried deprecation attributes; others were uncited direct
consequences of the listed canonical interface.  The deletion deliberately
breaks those unused downstream names rather than introducing replacement
wrappers.

| Removed declaration | Canonical replacement |
|---|---|
| `Edge.ofAdj_symm` | Split the endpoint order and use `Edge.ofAdj_of_lt` / `Edge.ofAdj_of_gt`. |
| `SectorBNT.Examples.singletonDecomp` | `singleSectorDecomposition` |
| `one_sub_mul_kraus_mul_eq_zero_of_transferMap_proj` | `Kraus.one_sub_mul_kraus_mul_eq_zero_of_mapLM_proj`, after `Kraus.mapLM_eq_transferMap` |
| `CoarseBlockingFrame.not_crossing_rb_and_rc` | The `red_disjoint_blue`, `red_disjoint_complement`, and `blue_disjoint_complement` fields of `CoarseBlockingFrame.IsPartition` |
| `CoarseBlockingFrame.not_crossing_rb_and_bc` | The pairwise-disjoint fields of `CoarseBlockingFrame.IsPartition` |
| `CoarseBlockingFrame.not_crossing_rc_and_bc` | The pairwise-disjoint fields of `CoarseBlockingFrame.IsPartition` |
| `coherentFrameOfRegions_isPartition` | Construct `CoarseBlockingFrame.IsPartition` directly as `⟨hrb, hrc, hbc, hcover⟩`. |
| `verticalStaircaseWindow_zero` | Expand the vertical definitions and use `staircaseWindow_zero`. |
| `verticalStaircaseWindow_last` | Expand the vertical definitions and use `staircaseWindow_last`. |
| `NormalTorusArcWindowInjectivityHypotheses.verticalStaircaseWindow_injective` | Expand `verticalStaircaseWindow` and apply `arcWindow_injective`. |
| `NormalTorusArcWindowInjectivityHypotheses.verticalStaircaseUnion_injective` | Rewrite by `verticalStaircaseUnion_eq_verticalRectangle` or `verticalStaircaseUnion_eq_horizontalRectangle`, then use the corresponding union-injectivity theorem. |
| `mem_verticalStaircaseWindow` | Expand `verticalStaircaseWindow` and use `mem_staircaseWindow`. |
| `verticalStaircaseWindow_subset_verticalStaircaseUnion` | Expand the vertical definitions and use `staircaseWindow_subset_staircaseUnion`. |
| `verticalStaircaseWindow_succ_subset_verticalStaircaseUnion` | Expand the vertical definitions and use `staircaseWindow_succ_subset_staircaseUnion`. |
| `verticalStaircaseWindow_subset_patch` | Expand the vertical definitions and use `staircaseWindow_subset_patch`. |
| `verticalStaircaseUnion_subset_patch` | Expand the vertical definitions and use `staircaseUnion_subset_patch`. |
| `biUnion_verticalStaircaseWindow_eq_patch` | Expand the vertical definitions and use `biUnion_staircaseWindow_eq_patch`. |
| `torusCoordinateSwapRegion_union` | Unfold `torusCoordinateSwapRegion` and use `Finset.map_union`. |
| `torusCoordinateSwap_isVertical` | `torusHorizontalNeighbor_coordinateSwap` together with `Edge.map_endpoints` |
| `torusCoordinateSwap_isHorizontal` | `torusVerticalNeighbor_coordinateSwap` together with `Edge.map_endpoints` |
| `torusCoordinateSwapRegion_biUnion` | Finset extensionality, `mem_torusCoordinateSwapRegion`, and `Finset.mem_biUnion` |
| `torusCoordinateSwapRegion_mono` | Unfold `torusCoordinateSwapRegion` and use `Finset.map_subset_map.mpr`. |
| `NormalTorusArcWindowInjectivityHypotheses.horizontalUnion_injective` | `arcRectangle_injective` at side lengths `(L + 1, K)` |
| `NormalTorusArcWindowInjectivityHypotheses.verticalUnion_injective` | `arcRectangle_injective` at side lengths `(L, K + 1)` |
| `mem_torusVerticalEdgeComplement` | Unfold the vertical regions, rewrite by `mem_torusCoordinateSwapRegion`, and use `mem_torusHorizontalEdgeComplement`. |
| `torusVerticalEdgeComplementPiece` | Map `torusHorizontalEdgeComplementPiece` by `torusCoordinateSwapRegion` if an explicit piece is needed. |
| `torusVerticalEdgeComplement_eq_biUnion_pieces` | Transport `torusHorizontalEdgeComplement_eq_biUnion_pieces` by `congrArg torusCoordinateSwapRegion`; the retained injectivity proof uses coordinate-swap transport directly. |

The three long crossing-exclusivity proofs in `CoherentFrameInstance.lean`
were particularly misleading duplication: their deprecation messages already
identified the partition fields as the mathematical argument.  Removing them
therefore exposes the underlying partition statement instead of maintaining a
second proof of it.

The declaration `torusCoordinateSwapRegion_torusArcRectangle` is retained with
the same name and statement, but now lives in `TorusWindowComplement.lean`.
This move breaks the narrower import surface of clients that imported only
`TorusCoordinateSwap.lean`; it is required to invert the dependency before the
vertical edge region can be defined by coordinate transport without a cycle.
