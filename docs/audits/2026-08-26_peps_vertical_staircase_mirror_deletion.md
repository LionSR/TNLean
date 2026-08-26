# PEPS vertical-staircase mirror and coordinate-swap transport deletion

This audit records the repository-local pass-through exception
(`docs/project_conventions.md` §Style) for the removal of
`TNLean/PEPS/TorusWindowFamilyVertical.lean` and
`TNLean/PEPS/TorusCoordinateSwap.lean`.

At the audited head neither file had a non-`Archive` consumer: no module under
`TNLean/` imported them except the generated aggregator `TNLean/PEPS.lean`, no
`\lean{...}` tag under `blueprint/src/` names any of the declarations below, and
neither `docs/glossary.md` nor `docs/paper-gaps/` cites them.

This closes the leftover of ledger entry D10 (closed 2026-07-23, PR #4634): the
transport re-derivation landed, but the mirror shells themselves were never
retired. The live vertical-staircase development —
`verticalStaircaseEdge_val` and `isCrossingEdge_verticalStaircase`
(`TNLean/PEPS/TorusWindowRegion.lean`),
`verticalStaircaseConsecutiveWindow_bondTransport_extend_eq`
(`TNLean/PEPS/TorusWindowBondTransport.lean`) and its `_uniform` companion
(`TNLean/PEPS/TorusWindowBondUniform.lean`) — works directly in
`torusArcRectangle` coordinates and is untouched.
`TNLean/PEPS/SquareLatticeCoordinateSwap.lean` is a separate, live surface and is
likewise untouched.

## Removed declarations with dated deprecation text

These carried `@[deprecated ... (since := "2026-07-30")]` in source; the
replacement is the text they already advertised.

| Removed declaration | Existing replacement |
|---|---|
| `verticalStaircaseWindow_zero` | expand `verticalStaircaseWindow` and use `staircaseWindow_zero` |
| `verticalStaircaseWindow_last` | expand the vertical-window definitions and use `staircaseWindow_last` |
| `NormalTorusArcWindowInjectivityHypotheses.verticalStaircaseWindow_injective` | expand `verticalStaircaseWindow` and apply `arcWindow_injective` |
| `NormalTorusArcWindowInjectivityHypotheses.verticalStaircaseUnion_injective` | rewrite with `verticalStaircaseUnion_eq_verticalRectangle` or `verticalStaircaseUnion_eq_horizontalRectangle`, then use the corresponding union-injectivity theorem |
| `mem_verticalStaircaseWindow` | expand `verticalStaircaseWindow` and use `mem_staircaseWindow` |
| `verticalStaircaseWindow_subset_verticalStaircaseUnion` | expand the vertical definitions and use `staircaseWindow_subset_staircaseUnion` |
| `verticalStaircaseWindow_succ_subset_verticalStaircaseUnion` | expand the vertical definitions and use `staircaseWindow_succ_subset_staircaseUnion` |
| `verticalStaircaseWindow_subset_patch` | expand the vertical definitions and use `staircaseWindow_subset_patch` |
| `verticalStaircaseUnion_subset_patch` | expand the vertical definitions and use `staircaseUnion_subset_patch` |
| `biUnion_verticalStaircaseWindow_eq_patch` | expand the vertical definitions and use `biUnion_staircaseWindow_eq_patch` |
| `torusCoordinateSwapRegion_union` | expand `torusCoordinateSwapRegion` and use `Finset.map_union` |
| `torusCoordinateSwap_isVertical` | `torusHorizontalNeighbor_coordinateSwap` together with `Edge.map_endpoints` |
| `torusCoordinateSwap_isHorizontal` | `torusVerticalNeighbor_coordinateSwap` together with `Edge.map_endpoints` |

## Removed declarations with no replacement needed

For each of the following the replacement is: **none needed — zero consumers;
the live vertical-staircase development in `TorusWindowRegion`,
`TorusWindowBondTransport`, and `TorusWindowBondUniform` works directly in
`torusArcRectangle` coordinates.**

Vertical window, patch, and union definitions and their geometry:

- `verticalStaircaseRightWindow`
- `verticalStaircaseLeftWindow`
- `verticalStaircasePatch`
- `verticalStaircaseWindow`
- `verticalStaircaseUnion`
- `verticalStaircaseUnion_eq_verticalRectangle`
- `verticalStaircaseUnion_eq_horizontalRectangle`

The coordinate-swap transport pack:

- `torusCoordinateSwapEquiv`
- `torusCoordinateSwapEquiv_apply`
- `torusCoordinateSwapEquiv_symm`
- `torusHorizontalNeighbor_coordinateSwap`
- `torusVerticalNeighbor_coordinateSwap`
- `torusCoordinateSwapRegion`
- `mem_torusCoordinateSwapRegion`
- `torusCoordinateSwapRegion_biUnion`
- `torusCoordinateSwapRegion_mono`
- `torusCoordinateSwapRegion_swap`
- `torusCoordinateSwapRegion_torusArcRectangle`
- `torusCoordinateSwap`
- `torusCoordinateSwap_apply`
- `torusCoordinateSwap_symm`

## Supersession of an earlier audit

`docs/audits/2026-07-30_peps_zero_reference_pass_through_audit.md` names several
of the declarations above in its *replacement* column. That audit now carries a
supersession line pointing here.
