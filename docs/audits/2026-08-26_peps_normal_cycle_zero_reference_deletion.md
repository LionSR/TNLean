# Normal-PEPS and cycle-MPS zero-reference and pass-through retirement

Date: 2026-08-26. Area: the non-Torus normal-PEPS, cycle-MPS, and
region-transport modules under `TNLean/PEPS/`.

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style together with a zero-reference deletion
slice of the open ledger entry S2 (`docs/proof_debt_ledger.md`, issue #4564).
At the audited head every declaration below had no non-`Archive` consumer, no
Blueprint `\lean{...}` tag, and no `\leanid{}` citation in
`docs/paper-gaps/`, so no transition declaration was left behind. Consumer
counts were taken by `rg -w` over `TNLean`, `blueprint`, `docs`, and `scripts`
and then confirmed by a full `lake build`.

## Pass-throughs at the interior-data assembly site

| Removed | Replacement |
|---|---|
| `TNLean.PEPS.normalSquareEdgeBlockingHypotheses_of_interiorData_injective_chain` | `(normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).injective_chain_at_edge e` applied at the use site, exactly as the retained siblings do in `TNLean/PEPS/NormalEdgeBlockingTranslated.lean` and `TNLean/PEPS/NormalSquarePEPSBlocking.lean` |
| `TNLean.PEPS.normalSquareEdgeBlockingHypotheses_of_interiorData_endpoint_disjoint_cover` | `(normalSquareEdgeBlockingHypotheses_of_interiorData h hUnion data).endpoint_disjoint_cover_at_edge e` applied at the use site |
| `TNLean.PEPS.normalSquareBlockingRegions_of_overlap` | `normalSquareBlockingRegions_of_TCover h (regionInjectivityUnionClosure_of_overlap A hpos) hWidth hHeight cover` (`TNLean/PEPS/NormalSquareInjectivity.lean`), which is the blueprint-cited survivor |
| `TNLean.PEPS.isTwoBlockInjective_regionTwoBlock_of_isVertexInjective` | `isTwoBlockInjective_regionTwoBlock A R (regionBlockedTensorInjective_of_isVertexInjective A R hA hpos)` |
| `TNLean.PEPS.NormalPEPSBlockingHypotheses.isTwoBlockInjective_redTwoBlock` | `isTwoBlockInjective_regionTwoBlock A (h.edgeBlocking.red e) (h.injective_chain_at_edge e).1` |
| `TNLean.PEPS.NormalPEPSBlockingHypotheses.isTwoBlockInjective_blueTwoBlock` | `isTwoBlockInjective_regionTwoBlock A (h.edgeBlocking.blue e) (h.injective_chain_at_edge e).2.1` |
| `TNLean.PEPS.NormalPEPSBlockingHypotheses.isTwoBlockInjective_complementTwoBlock` | `isTwoBlockInjective_regionTwoBlock A (h.edgeBlocking.complement e) (h.injective_chain_at_edge e).2.2` |
| `TNLean.PEPS.NormalPEPSBlockingHypotheses.redTwoBlock` | `regionTwoBlock A (h.edgeBlocking.red e)` |
| `TNLean.PEPS.NormalPEPSBlockingHypotheses.blueTwoBlock` | `regionTwoBlock A (h.edgeBlocking.blue e)` |
| `TNLean.PEPS.NormalPEPSBlockingHypotheses.complementTwoBlock` | `regionTwoBlock A (h.edgeBlocking.complement e)` |

## Zero-reference declarations with no survivor

| Removed | Replacement |
|---|---|
| `TNLean.PEPS.edgeEndpointLocalVirtualOpOfPhysicalOp_eq_of_projected_realization_eqAt` | none needed; the conjunction was the pair of `edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eqAt` and `edgeRightLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eqAt`, both retained |
| `TNLean.PEPS.cycleGaugeOfEdgeGauge_edgeGaugeOfCycleGauge` | none; the round-trip identity was never consumed by the cycle Fundamental Theorem |
| `TNLean.PEPS.pos_d_of_isNBlkInjective` | none; the argument is two lines from `MPSTensor.exists_ne_zero_of_isNBlkInjective` where a positive physical dimension is actually wanted |
| `TNLean.PEPS.not_add_one_eq_and_add_one_eq` | none; the retained neighbouring cycle-arithmetic lemmas cover the consumed cases |
| `TNLean.PEPS.Region_map_mono` | `Finset.map_subset_map.mpr` (Mathlib, `Mathlib/Data/Finset/Image.lean`), since `Region.map φ R = R.map φ.toEquiv.toEmbedding` |
| `TNLean.PEPS.isCrossingEdge_horizontalTranslatedEdge_blockingDatum_interior` | `isCrossingEdge_normalSquareHorizontalTranslatedEdge`, retained in the same file |
| `TNLean.PEPS.isCrossingEdge_verticalTranslatedEdge_blockingDatum_interior` | `isCrossingEdge_normalSquareVerticalTranslatedEdge`, retained in the same file |

## Retained on purpose

`TNLean.PEPS.normalSquareEdgeBlockingHypotheses_of_interiorData` is kept: it
carries a Blueprint `\lean{...}` tag in
`blueprint/src/chapter/ch24_peps_ft_normal_square_rectangular_injectivity.tex`
and is cited twice in `docs/paper-gaps/peps_normal_ft_section3_route.tex`. The
two retired accessors above it were only its projections.

Five names that a `\lean{}`-only scan reported as unreferenced were withdrawn
from this slice because `docs/paper-gaps/peps_normal_ft_section3_route.tex`
cites them through `\leanid{}`: `edgeGauge_unique_scalar`,
`transportBlockingDataAlong_complement`,
`regionBlockedTensorInjective_host_transportBlockingDataAlong`,
`regionComplement_comparison_of_vertexInjective`, and
`MPSTensor.exists_bondOperator_of_intertwine`. Future S2 slices must grep
`docs/paper-gaps/` as well as `blueprint/src/`.

The Blueprint tags at
`blueprint/src/chapter/ch24_peps_ft_region_transfer_covariance.tex` naming
`TNLean.PEPS.complementTwoBlock` and
`TNLean.PEPS.isTwoBlockInjective_complementTwoBlock` were checked and left
untouched: they resolve to the vertex-complement declarations in
`TNLean/PEPS/FundamentalTheorem/OneVertexComparison.lean`, not to the
edge-centred wrappers retired here, whose full names carried the
`NormalPEPSBlockingHypotheses` namespace prefix.

## Deferred

`TNLean.PEPS.edgeGaugeOfCycleGauge` in
`TNLean/PEPS/CycleMPSFundamentalTheorem.lean` became zero-reference once its
round-trip identity was retired. It is left in place, still described by the
module docstring, for a follow-up slice rather than widening this one.

The identically-shaped unreferenced accessors
`normalSquareEdgeBlockingHypotheses_injective_chain_of_marginCovers` and
`normalSquareEdgeBlockingHypotheses_endpoint_disjoint_cover_of_marginCovers`
in `TNLean/PEPS/NormalEdgeBlockingTranslated.lean` are the same shape and need
their own verification pass.

## Imports

No import was removed. `TNLean/PEPS/NormalEdgeGauge.lean` keeps
`TNLean.PEPS.NormalBlocking` even though its own surviving content no longer
needs it: its two direct importers and their transitive consumers reach PEPS
material through that path.
