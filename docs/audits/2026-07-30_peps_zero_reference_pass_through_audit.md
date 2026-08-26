# PEPS zero-reference pass-through audit

This audit records the repository-local deprecation exception used by PR #5112.
Each declaration below was an exact pass-through with no independent
mathematical content. At the audited head, it had no non-`Archive` consumer and
no Blueprint `\lean{...}` tag.

| Removed declaration | Existing replacement |
|---|---|
| `legEquivRed_eq_legEquivComplement_on_rc_single` | `legEquivRed_eq_legEquivComplement_on_rc` with the same configuration in both arguments |
| `legEquivBlue_eq_legEquivComplement_on_bc_single` | `legEquivBlue_eq_legEquivComplement_on_bc` with the same configuration in both arguments |
| `Region_map_torusCoordinateSwap_torusArcRectangle` | unfold `Region.map`, then use `torusCoordinateSwapRegion_torusArcRectangle` |
| `torusCoordinateSwapRegion_horizontalStaircaseRightWindow` | unfold `verticalStaircaseRightWindow`; the equality is definitional |
| `torusCoordinateSwapRegion_horizontalStaircaseLeftWindow` | unfold `verticalStaircaseLeftWindow`; the equality is definitional |
| `torusCoordinateSwapRegion_horizontalStaircasePatch` | unfold `verticalStaircasePatch`; the equality is definitional |
| `torusCoordinateSwapRegion_staircaseWindow` | unfold `verticalStaircaseWindow`; the equality is definitional |
| `torusCoordinateSwapRegion_staircaseUnion` | unfold `verticalStaircaseUnion`; the equality is definitional |
| `Region_map_torusCoordinateSwap_staircaseWindow` | unfold `Region.map` and `verticalStaircaseWindow`; the equality is definitional |
| `Region_map_torusCoordinateSwap_staircaseUnion` | unfold `Region.map` and `verticalStaircaseUnion`; the equality is definitional |
| `Region_map_torusCoordinateSwap_horizontalStaircasePatch` | unfold `Region.map` and `verticalStaircasePatch`; the equality is definitional |
| `IsVertexInjective.localTensorMap_ker_eq_bot` | `localTensorMap_ker_eq_bot_of_linearIndependent (hA v)` |
| `physRealizeLocalOp_comp` | `physRealizeLocalOpAt_comp A (hA v)` |
| `localProjector_idempotent` | `localProjectorAt_idempotent A (hA v)` |
| `localVirtualOpOfPhysicalOp_eq_of_projected_action_eq` | `localVirtualOpOfPhysicalOpAt_eq_of_projected_action_eq A (hA v)` |

All other public declarations considered by this wave contain independent
mathematical statements or proofs. They remain available with dated
deprecations rather than using this exception.

## Supersession (2026-08-26)

The replacement names in the rows for
`Region_map_torusCoordinateSwap_torusArcRectangle`,
`torusCoordinateSwapRegion_horizontalStaircaseRightWindow`,
`torusCoordinateSwapRegion_horizontalStaircaseLeftWindow`,
`torusCoordinateSwapRegion_horizontalStaircasePatch`,
`torusCoordinateSwapRegion_staircaseWindow`,
`torusCoordinateSwapRegion_staircaseUnion`,
`Region_map_torusCoordinateSwap_staircaseWindow`,
`Region_map_torusCoordinateSwap_staircaseUnion`, and
`Region_map_torusCoordinateSwap_horizontalStaircasePatch` —
`torusCoordinateSwapRegion_torusArcRectangle`,
`verticalStaircaseRightWindow`, `verticalStaircaseLeftWindow`,
`verticalStaircasePatch`, `verticalStaircaseWindow`, and
`verticalStaircaseUnion` — were themselves removed on 2026-08-26 with
`TNLean/PEPS/TorusWindowFamilyVertical.lean` and
`TNLean/PEPS/TorusCoordinateSwap.lean`. See
`docs/audits/2026-08-26_peps_vertical_staircase_mirror_deletion.md`.

The replacement names in the rows for
`legEquivRed_eq_legEquivComplement_on_rc_single` and
`legEquivBlue_eq_legEquivComplement_on_bc_single` —
`legEquivRed_eq_legEquivComplement_on_rc` and
`legEquivBlue_eq_legEquivComplement_on_bc` — were themselves removed on
2026-08-26 as zero-reference. See
`docs/audits/2026-08-26_peps_regionblock_zero_reference_deletion.md`.
