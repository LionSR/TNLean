# PEPS restored-layer retirement (merge-artefact re-deletion)

On 2026-09-19 four bounded simplifications landed on `main`: the retirement of
the vertex-injective forwarder layer in `TNLean/PEPS/VirtualInsertion.lean`
(recorded in
`docs/audits/2026-09-19_peps_virtual_insertion_forwarder_retirement.md`), the
deletion of the unused vertical staircase end pair in
`TNLean/PEPS/TorusWindowRegion.lean` (recorded in
`docs/audits/2026-08-26_peps_vertical_staircase_mirror_deletion.md`), the
replacement of an eleven-line set-difference proof in
`TNLean/PEPS/TorusWindowChain4.lean` by the Mathlib statement
`Finset.sdiff_union_sdiff_cancel` (recorded in
`docs/audits/2026-09-19_upstream_shadow_removals.md`), and a docstring
correction in `TNLean/PEPS/RegionBlock/ThreeBlockTransfer.lean` (recorded in
`docs/audits/2026-09-19_peps_regionblock_dead_closures.md`). Hours later an
unrelated branch merged with bot commits that re-added all four pieces
verbatim while resolving conflicts in two blueprint chapter files; the branch's
own change touched no PEPS file, and no review comment, ledger line, or audit
note records a reason for the restoration. The restoration is a merge
artefact, not a retained-on-purpose decision, and
`docs/project_conventions.md` keeps no compatibility wrappers, so this pass
deletes the restored layer again.

## Removed declarations

All Lean removals are re-deletions of the earlier removals; the replacement
column names the surviving declaration each call site would use.

From `TNLean/PEPS/VirtualInsertion.lean` (eleven one-line forwarders, each
whose body is the per-vertex theorem applied at one vertex, plus the restored
`Main contents` bullet for `physRealizeLocalOp_spec`):

| Removed declaration | Existing replacement |
|---|---|
| `physRealizeLocalOp_spec` | `physRealizeLocalOpAt_spec A (hA v)` |
| `localIncidentMatrixOp_physicalRealization` | `localIncidentMatrixOp_physicalRealizationAt A (hA v)` |
| `physRealizeLocalOp_injective` | `physRealizeLocalOpAt_injective A (hA v)` |
| `localVirtualOpOfPhysicalOp_spec` | `localVirtualOpOfPhysicalOpAt_spec A (hA v)` |
| `localVirtualOpOfPhysicalOp_realizes_of_projector` | `localVirtualOpOfPhysicalOpAt_realizes_of_projector A (hA v)` |
| `localVirtualOpOfPhysicalOp_eq_of_realizes` | `localVirtualOpOfPhysicalOpAt_eq_of_realizes A (hA v)` |
| `localVirtualOpOfPhysicalOp_eq_iff_projected_action_eq` | `localVirtualOpOfPhysicalOpAt_eq_iff_projected_action_eq A (hA v)` |
| `localVirtualOpOfPhysicalOp_physRealizeLocalOp` | `localVirtualOpOfPhysicalOpAt_physRealizeLocalOpAt A (hA v)` |
| `physRealizeLocalOp_localVirtualOpOfPhysicalOp` | `physRealizeLocalOpAt_localVirtualOpOfPhysicalOpAt A (hA v)` |
| `localVirtualOpOfPhysicalOp_eq_of_projected_realization_eq` | `localVirtualOpOfPhysicalOpAt_eq_of_projected_realization_eq A (hA v)` |
| `localVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq` | `localVirtualOpOfPhysicalOpAt_eq_iff_projected_realization_eq A (hA v)` |

From `TNLean/PEPS/TorusWindowRegion.lean` (the vertical staircase end pair,
with its section header; the horizontal pair carries the window chain):

| Removed declaration | Existing replacement |
|---|---|
| `verticalStaircaseEdge_val` | `horizontalStaircaseEdge_val` (transposed argument) |
| `isCrossingEdge_verticalStaircase` | `isCrossingEdge_horizontalStaircase`; the vertical route runs through `isCrossingEdge_torusVerticalEdge` in `TNLean/PEPS/TorusEdgeBlockingCrossing.lean` |

Also removed there: the restored module-docstring sentence claiming the
vertical comparison goes through the reference-blocking route cited above; the
route it cites names `isCrossingEdge_torusVerticalEdge` (imported) and
`isCrossingEdge_torusVerticalRectangleBlockingDatum` (defined in
`TNLean/PEPS/TorusRectangleReferenceData.lean`, not imported by this file),
and the sentence duplicated the preceding paragraph.

In `TNLean/PEPS/TorusWindowChain4.lean` no declaration is removed: the proof
of `threeBlockBlueCoeff_comp` again closes the union identity
`(S \ R) ∪ (P \ S) = P \ R` with
`(Finset.union_comm _ _).trans (Finset.sdiff_union_sdiff_cancel hSP hRS)`
(Mathlib, `Mathlib/Data/Finset/SDiff.lean`) instead of an eleven-line
`by ext w; …` argument. The statement and the blueprint tag are unchanged.

In `TNLean/PEPS/RegionBlock/ThreeBlockTransfer.lean` the module docstring
again reads "into the per-edge gauge of
`TNLean.PEPS.RegionBlock.RegionReconcile`": the restored wording's
"three-block transfer engine" names nothing in `RegionReconcile.lean`, and
`ThreeBlockReconcile.lean` no longer exists in `RegionBlock/`.

## Checked

- Word-boundary search of each removed name over `TNLean/`, `blueprint/src/`,
  `docs/`, and `scripts/` (excluding historical audit notes) returns no hit
  outside the declaring file. The earlier substring hit for
  `localIncidentMatrixOp_physicalRealization` in three insertion files was the
  surviving `…At` declaration.
- Blueprint census: every `\lean{...}` payload in
  `blueprint/src/chapter/ch24_peps_ft_foundations.tex` names a per-vertex
  survivor; the `\label`/`\uses` strings that mention removed names are node
  labels, which keep their names. `threeBlockBlueCoeff_comp` is tagged in
  `blueprint/src/chapter/ch24_peps_ft_torus_corner_cancellation.tex` and only
  its proof text changed. No tag was added, redirected, or removed.
- `python3 scripts/blueprint_lean_sync.py --ci` passes.
- The PEPS aggregator and the direct importers of the four edited modules
  build clean through the linter-bearing build.

## Retained

- `localProjector_apply_localTensorMap` in `VirtualInsertion.lean`: a
  pass-through of the same shape, but the bare `simp` calls in
  `TNLean/PEPS/LocalGauge.lean` fire on it (see
  `docs/audits/2026-08-27_peps_cycle_edge_simp_retirement.md`).
- The definitions `physRealizeLocalOp`, `localProjector`,
  `localVirtualOpOfPhysicalOp`, and `localLeftInverse`: untagged conveniences
  used by `InsertionRealization.lean` and `LocalGauge.lean`.
- The 2026-09-19 retirement note, with its clearance paragraph amended to
  record the restoration and this re-retirement.

## Deferred

The proof-debt ledger's S3 entry still lists `ThreeBlockReconcile` and
`BondLocalFromReconcile` in its `What` line; that correction is owned by the
open three-block tracking issue and is reported there rather than edited here.
