# PEPS RegionBlock attribute-carrying zero-reference batch

`docs/audits/2026-08-26_peps_regionblock_zero_reference_deletion.md` opens by
recording that none of the eight declarations it removed carried `@[simp]`,
`@[grind]`, or `@[ext]`, and that none was an instance. That exclusion was a
deferral, not a retention ruling: an attribute-carrying declaration can be
consumed by name-free tactic invocations, so a grep verdict cannot settle it and
only a root build can. This note records the build-checked follow-up.

Twenty-five declarations under `TNLean/PEPS/RegionBlock/` were name-level
zero-reference — the definition site was the only occurrence anywhere in
`TNLean/`, `blueprint/`, or `docs/` — and each carried either `@[simp]` on a
`rfl` projection or was a `Fintype` instance defined by `inferInstance` over a
`@[reducible] abbrev` pi-type. All twenty-five were deleted in one batch, and a
root `lake build` was run over the whole library.

## Deleted set

Line numbers cite the audited head `ffba2d758`.

| Removed declaration | Location at the audited head |
|---|---|
| `TNLean.PEPS.CoarseBlockingFrame.regionOf_zero` | `TNLean/PEPS/RegionBlock/CoarseThreeSite.lean:202` |
| `TNLean.PEPS.CoarseBlockingFrame.regionOf_one` | `TNLean/PEPS/RegionBlock/CoarseThreeSite.lean:204` |
| `TNLean.PEPS.CoarseBlockingFrame.regionOf_two` | `TNLean/PEPS/RegionBlock/CoarseThreeSite.lean:206` |
| `TNLean.PEPS.CoarseBlockingFrame.coarseTensor_bondDim` | `TNLean/PEPS/RegionBlock/CoarseThreeSite.lean:245` |
| `TNLean.PEPS.instFintypeCrossingConfig` | `TNLean/PEPS/RegionBlock/CoarseThreeSite2.lean:94` |
| `TNLean.PEPS.CoarseBlockingFrame.edgeRegions_rb` | `TNLean/PEPS/RegionBlock/CoarseThreeSite2.lean:117` |
| `TNLean.PEPS.CoarseBlockingFrame.edgeRegions_rc` | `TNLean/PEPS/RegionBlock/CoarseThreeSite2.lean:119` |
| `TNLean.PEPS.CoarseBlockingFrame.edgeRegions_bc` | `TNLean/PEPS/RegionBlock/CoarseThreeSite2.lean:121` |
| `TNLean.PEPS.CoarseBlockingFrame.toThreeBlockGeometry_red` | `TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean:126` |
| `TNLean.PEPS.CoarseBlockingFrame.toThreeBlockGeometry_blue` | `TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean:128` |
| `TNLean.PEPS.CoarseBlockingFrame.toThreeBlockGeometry_complement` | `TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean:130` |
| `TNLean.PEPS.incidentRB0_fst` | `TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean:281` |
| `TNLean.PEPS.incidentRC0_fst` | `TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean:282` |
| `TNLean.PEPS.incidentRB1_fst` | `TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean:283` |
| `TNLean.PEPS.incidentBC1_fst` | `TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean:284` |
| `TNLean.PEPS.incidentRC2_fst` | `TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean:285` |
| `TNLean.PEPS.incidentBC2_fst` | `TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean:286` |
| `TNLean.PEPS.overrideEdge_coarse_rb` | `TNLean/PEPS/RegionBlock/CoarseThreeSite7.lean:309` |
| `TNLean.PEPS.RegionInsertionTransfer.fwdAlgHom_apply` | `TNLean/PEPS/RegionBlock/Algebra.lean:422` |
| `TNLean.PEPS.RegionInsertionTransfer.fwdAlgEquiv_apply` | `TNLean/PEPS/RegionBlock/Algebra.lean:452` |
| `TNLean.PEPS.regionBoundaryEdgeComplEquiv_apply_coe` | `TNLean/PEPS/RegionBlock/Insertion.lean:88` |
| `TNLean.PEPS.regionBoundaryEdgeDoubleComplEquiv_apply_coe` | `TNLean/PEPS/RegionBlock/Recovery6.lean:97` |
| `TNLean.PEPS.instFintypeRegionPhysicalConfig` | `TNLean/PEPS/RegionBlock/Basic.lean:106` |
| `TNLean.PEPS.instFintypeTouchConfig` | `TNLean/PEPS/RegionBlock/KernelDescent.lean:303` |
| `TNLean.PEPS.instFintypeExteriorConfig` | `TNLean/PEPS/RegionBlock/KernelDescent.lean:312` |

Each removed name is replaced by the definitional unfolding it stated. A `rfl`
projection of a pattern-matching definition (`regionOf_zero` and its two
siblings, `edgeRegions_rb` and its two siblings, the six `incident*_fst`) is
recovered by `rfl` at any use site; a structure-field projection
(`coarseTensor_bondDim`, the three `toThreeBlockGeometry_*`, the two
`fwdAlg*_apply`, the two boundary-edge-equivalence coercions) likewise. Each
deleted `Fintype` instance is replaced by the instance search already finds:
`Pi.instFintype` over the underlying pi-type, which is what the `inferInstance`
body was reporting. `overrideEdge_coarse_rb` is replaced by the general
`overrideEdge_edge` (`TNLean/PEPS/RegionBlock/CoarseThreeSite7.lean`), of which
it was a coarse-graph instance.

## Restored set: empty

No restores were needed. The root `lake build` was clean on the first attempt
across all 10,365 jobs, with every reverse dependent of the nine edited modules
rebuilt — the `CoarseThreeSite8`--`CoarseThreeSite11`, `Recovery*`,
`CoherentFrameInstance`, and `UnionInjectivity*` modules among them.

This contradicts the prediction that accompanied the batch, which named
`toThreeBlockGeometry_red`/`_blue`/`_complement` and
`fwdAlgHom_apply`/`fwdAlgEquiv_apply` as the likeliest survivors on the grounds
that their left-hand sides occur in live proofs. They do occur, but the goals in
question close on definitional unfolding without the named lemmas in the default
simp set. The mismatch is recorded here because an empty restored set is the
outcome that carries information: it means none of the twenty-five was load
bearing for any tactic invocation in the library, and there is therefore no
tactic pattern to promote into `docs/tactic_patterns.md` from this batch.

## No definition lost its last consumer

Every underlying definition whose projection was deleted survives with
independent uses: `regionOf`, `edgeRegions`, `coarseTensor`, `toThreeBlockGeometry`,
the six `incident*` super-edge definitions, `overrideEdge`, `fwdAlgHom`,
`fwdAlgEquiv`, `regionBoundaryEdgeComplEquiv`, and
`regionBoundaryEdgeDoubleComplEquiv`. The abbreviations behind the deleted
`Fintype` instances — `CrossingConfig`, `RegionPhysicalConfig`, `TouchConfig`,
`ExteriorConfig` — are all still in use, and their instance needs are met by
search.

## Deliberately retained

`instFintypeRegionBoundaryConfig` (`TNLean/PEPS/RegionBlock/Basic.lean`) has the
same `inferInstance` shape and no production reference, but a comment inside
`regionInsertedCoeff` (`TNLean/PEPS/RegionBlock/Insertion.lean`) names it as the
concrete instance distinguishing two otherwise identical `Finset.univ`s, and the
bridging step there is written around that distinction. Removing it would change
which instance elaboration picks at that step, so it is out of scope for a
zero-reference pass and left in place.

`regionBoundaryEdgeComplEquiv_symm_apply_coe`
(`TNLean/PEPS/RegionBlock/Insertion.lean`) is the sibling of a deleted lemma but
is not itself zero-reference, and is untouched.
