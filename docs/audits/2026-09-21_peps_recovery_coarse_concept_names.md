# Concept names for the remaining PEPS recovery and coarse-frame sequels

Second slice of the rename-and-merge of the numbered `PEPS` chains recorded as
section 10 of the numbered-sequel debt item, continuing
`docs/audits/2026-09-19_peps_overlap_chain_concept_names.md`. Three adjacent
stage pairs of the `PEPS/RegionBlock` development are merged into concept-named
modules, and the last two `2`-suffixed modules of the plan are renamed by their
content. No declaration is renamed, added, or removed, so every blueprint
`\lean{...}` tag keeps its target.

## Merged modules

| Absorbed modules | Surviving module |
|---|---|
| `TNLean/PEPS/RegionBlock/Recovery5.lean`, `TNLean/PEPS/RegionBlock/Recovery6.lean` | `TNLean/PEPS/RegionBlock/RecoveryOutRegionEndpoint.lean` |
| `TNLean/PEPS/RegionBlock/Recovery10.lean`, `TNLean/PEPS/RegionBlock/Recovery11.lean` | `TNLean/PEPS/RegionBlock/RecoveryCoefficientTransfer.lean` |
| `TNLean/PEPS/RegionBlock/CoarseThreeSite2.lean`, `TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean` | `TNLean/PEPS/RegionBlock/CoarseThreeSiteCoherentFrame.lean` |

Each pair is phase-honest. The first pair is the out-of-region endpoint of a
boundary edge: the endpoint identity together with the blocked-region tensor map
and its left inverse, and then the double-complement transport that realizes the
region-inserted coefficient through that endpoint. The second pair is the
coefficient transfer: the transfer coefficient, its v-side and complement rows
and the double factorization, and then the incident-matrix form of the same
object. The third pair is the coherent coarse blocking frame: the crossing
edges, the partner regions and the coarse state coefficient as a product of
three region weights, and then the partition hypothesis and the three-region
merge collapse of that product.

Within each pair the two modules share one `open scoped`, `namespace`, and
`variable` preamble verbatim, so no merge needs a `section` wrapper and no
signature acquires or loses an instance argument. Neither member of any pair
declares a `private` name, and no short name is declared in both members, so the
concatenation introduces no shadowing. Each merged module keeps one copyright
header, one import block, one module docstring, and one References block; the
absorbed narratives become sections of the surviving docstring and the duplicate
References blocks are dropped. The surviving files are 549, 821, and 729 lines,
all under the file-length cap.

The merges are cone-neutral. `Recovery6` imported only `Recovery5`, `Recovery11`
imported only `Recovery10`, and the two extra imports of `CoarseThreeSite3`
(`Recovery` and `UnionInjectivityGeneral`) already lay inside the import cone of
`CoarseThreeSite2`, so no importer of a surviving module gains a module it did
not already compile against.

## Renamed modules

| Old path | New path |
|---|---|
| `TNLean/PEPS/CoherentFrameInstance2.lean` | `TNLean/PEPS/BlockingDataEdgeGauge.lean` |
| `TNLean/PEPS/RegionBlock/GaugeInjectivity2.lean` | `TNLean/PEPS/RegionBlock/GaugeInjectivityBoundaryCoupling.lean` |

Neither module can be merged into its predecessor: `CoherentFrameInstance.lean`
is 879 lines and `GaugeInjectivity.lean` is 887, so either merge would exceed
the cap. Both new names state the mathematical responsibility the modules
already carry. The first assembles the per-edge gauge of two one-edge blocking
data through the coherent-frame interface; its docstring sentence describing the
split as a line-budget continuation is replaced by a description of what it
reads from its predecessor. The second states the boundary-coupling form of the
gauged blocked-region weight, the invertibility of the coupling matrix, and the
resulting preservation of blocked-region linear independence.

## Allowlist

`NUMBERED_DEBT_ALLOWLIST` in `scripts/check_numbered_lean_files.py` is a ratchet
that only shrinks. Eight entries are retired in the same change:
`Recovery5.lean`, `Recovery6.lean`, `Recovery10.lean`, `Recovery11.lean`,
`CoarseThreeSite2.lean`, `CoarseThreeSite3.lean`, `CoherentFrameInstance2.lean`,
and `GaugeInjectivity2.lean`, leaving 21 of the previous 29.

## What was checked

Outside the generated aggregators, the importers of the absorbed and renamed
modules are `PhysicalOperation.lean`, `Recovery7.lean`,
`BlockRangeCoincidence.lean`, `ThreeBlockResonate.lean`, `RegionReconcile.lean`,
`UnionInjectivityGeneral.lean`, `TorusEdgeBlockingCrossing.lean`,
`NormalEdgeSingleCrossing.lean`, `RegionTransportData.lean`,
`CycleBlockingData.lean`, `CoarseThreeSite4.lean`, `NormalAbsorbedFamily.lean`,
`NormalBondDimension.lean`, `NormalEdgeGaugeFamily.lean`,
`TorusGaugedWeightCovariance.lean`,
`NormalSquareUnconditionalFundamentalTheorem.lean`, and
`NormalComparisonScalar.lean`; all are retargeted. The docstring cross-references
in `Recovery7.lean`, `Recovery9.lean`, `BlockCoeffTransfer.lean`,
`RegionReconcile.lean`, `ThreeBlockResonate2.lean`, `CoarseThreeSite4.lean`, and
`CoherentFrameInstance.lean` are retargeted to the surviving names, and the
cross-references that became internal to a merged module are dropped rather than
left pointing at the module that now contains them.

Blueprint exposure of this material is by declaration, never by path: no
blueprint source cites any of the eight paths, and the declaration inventory is
unchanged, so the blueprint and Lean declaration sets remain in sync. The
`TNLean.PEPS` aggregator, which imports every module of the development, builds
clean with the package linter options.

## Retained and deferred

The remaining numbered modules of the two chains stay numbered and allowlisted.
The `Recovery` pairs `{4, 5}`, `{6, 7}`, `{8, 9}` and the `CoarseThreeSite`
pairs `{5, 6}` and `{8, 9}` remain refused: each cuts across the mathematical
phase its two docstrings name, and `CoarseThreeSite5.lean` and
`CoarseThreeSite6.lean` additionally carry different `variable` preambles, so
joining them would change tagged signatures. With this slice the whole section
10 plan is landed; what is left in the allowlist is the refused set plus the
modules too long to merge.

Dated audit notes that cite the old paths are left as written: they record the
state of the development on their own date and are not living references. The
living citation in `docs/tactic_patterns.md` is updated to the new path and line.
