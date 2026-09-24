# PEPS RegionBlock: the three-block resonate engine file

`TNLean/PEPS/RegionBlock/ThreeBlockResonate.lean` (874 lines, twenty-three
declarations) is removed in full. It was the edge-level resonate engine of the
normal PEPS Fundamental Theorem — the route the proof-debt ledger records under
S3 as a specialization of the source's union-injectivity lemma rather than the
lemma itself: it fixes a distinguished edge through a `NormalEdgeBlockingData`
where arXiv:1804.04964, Section 3 works over an arbitrary partition. The general
partition route (`UnionInjectivityGeneral*`) proves the source statement over a
bare `ThreeBlockGeometry` and recovers this one as a special case. The file
carried no `sorry` and no `axiom`.

The third S3 slice (#7875, merged as #7924) deleted the file's continuation
`ThreeBlockResonate2.lean` and retargeted the import edge of
`TNLean/PEPS/RegionBlock/UnionInjectivity.lean` at this file. This pass
re-verified the consumer census, the import edges, and the blueprint tags at
that post-#7924 tree before editing, since the pre-#7875 assumptions no longer
hold.

## What was checked before the deletion

Every one of the twenty-three declaration names was searched across `TNLean`,
`docs`, `blueprint`, and `scripts`, and each external match was attributed by
the namespace in scope at its use site. Only three declarations have code
consumers outside the file: `regionBlockedTensorInjective_red` (six consumers:
`NormalAbsorbedFamily.lean`, `ThreeBlockTransfer.lean` twice,
`NormalGeneralFundamentalTheorem.lean`, `NormalEdgeGaugeFamily.lean`, and
`NormalSquareEdgeCoeff.lean` twice) and `regionBlockedTensorInjective_blue` /
`regionBlockedTensorInjective_complement` (the union lemma of
`UnionInjectivity.lean`). Every external match on the other twenty names is
either a distinct `ThreeBlockGeometry`-namespaced declaration of
`UnionInjectivityGeneral.lean`, `UnionInjectivityGeneralBlue.lean`, or
`UnionInjectivityGeneral2.lean` sharing the short name (in particular
`threeBlockBlueCoeff`, whose receiver hits are all geometry-native), a docstring
mention, or a `docs/paper-gaps` citation of the namespaced form. No twin
declaration of the three live names exists elsewhere in the tree.

No Blueprint `\lean{...}` tag cites any of the twenty-three names (census via
`blueprint_lean_sync` over the tagged declarations). `docs/paper-gaps` cites
only `ThreeBlockGeometry.*` forms and `threeBlockBlueCoeff_comp`.

The file's only importers were `UnionInjectivity.lean` and the generated
aggregator `TNLean/PEPS/RegionBlock.lean`. Dropping the import edge from
`UnionInjectivity.lean` entirely loses `BlockRangeCoincidence` as the only
module of its former cone, and the file uses nothing from it;
`ThreeBlockTransfer.lean` reaches `BlockRangeCoincidence` through
`BlockCoeffTransfer.lean`. The remaining closure already contains
`UnionClosure` (which declares `regionInjectivityDataOf` and
`regionInjectivityDataOf_isInjective`) and `NormalEdgeBlockingData`, so the
three relocated lemmas need no new import and no new leaf module; a direct
elaboration of the edited file confirms this.

Three removed declarations carry attributes (`@[simp]
threeBlockComplPhysical_apply_blue`, `@[simp] threeBlockComplPhysical_apply_not_blue`,
and `@[simp] redBoundaryEdge_coe`). The build-check caveat for
attribute-carrying lemmas does not apply: the LHS heads
`threeBlockComplPhysical` and `redBoundaryEdge` have no mention in any
surviving module — every external hit is the `ThreeBlockGeometry.complPhysical`
twin or a docstring. The final proof that no surviving proof silently depended
on the removed simp lemmas is CI's root build.

## Removed declarations and their replacements

The three live declarations relocate into `UnionInjectivity.lean` with
byte-identical statements and docstrings; their fully qualified names are
unchanged, so every consumer resolves as before.

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.regionBlockedTensorInjective_red` | same name, now declared in `UnionInjectivity.lean` |
| `TNLean.PEPS.regionBlockedTensorInjective_blue` | same name, now declared in `UnionInjectivity.lean` |
| `TNLean.PEPS.regionBlockedTensorInjective_complement` | same name, now declared in `UnionInjectivity.lean` |
| `TNLean.PEPS.threeBlockComplPhysical` | none needed: the fused blue/complement physical leg, superseded by `TNLean.PEPS.ThreeBlockGeometry.complPhysical` (`UnionInjectivityGeneral.lean`) |
| `TNLean.PEPS.threeBlockComplPhysical_apply_blue` | none needed: `@[simp]` projection of the fused leg; twin is `ThreeBlockGeometry.complPhysical_apply_blue` |
| `TNLean.PEPS.threeBlockComplPhysical_apply_not_blue` | none needed: `@[simp]` projection of the fused leg; twin is `ThreeBlockGeometry.complPhysical_apply_not_blue` |
| `TNLean.PEPS.sdiff_red_eq_blue_union_complement` | none needed: twin is `ThreeBlockGeometry.sdiff_red_eq_blue_union_complement` |
| `TNLean.PEPS.prod_sdiff_red_eq_blue_mul_complement` | none needed: twin is `ThreeBlockGeometry.prod_sdiff_red_eq_blue_mul_complement` |
| `TNLean.PEPS.regionBlockedWeight_threeBlockComplPhysical_eq` | none needed: the geometry route proves the weight split inside `ThreeBlockGeometry.prod_sdiff_red_eq_blue_mul_complement` and the smul-factorization chain below; no surviving consumer |
| `TNLean.PEPS.isRegionBoundaryEdge_red_edge` | none needed: the crossing edge packaged as a boundary edge of the red block; no surviving consumer |
| `TNLean.PEPS.redBoundaryEdge` | none needed: the same packaging as a subtype value; no surviving consumer |
| `TNLean.PEPS.redBoundaryEdge_coe` | none needed: `@[simp]` coercion lemma of the same packaging; no surviving consumer |
| `TNLean.PEPS.threeBlockInsertedCoeff` | none needed: the three-block inserted coefficient; its consumer was the deleted continuation file |
| `TNLean.PEPS.threeBlockInsertedCoeff_eq_regionInsertedCoeff` | none needed: the bridge to `regionInsertedCoeff`; its consumer was the deleted continuation file |
| `TNLean.PEPS.blueProd_eq_regionMerge_complement` | none needed: twin is `ThreeBlockGeometry.blueProd_eq_regionMerge_complement` |
| `TNLean.PEPS.hostLabel_p2_eq_hostLabel_regionMerge_complement` | none needed: twin is `ThreeBlockGeometry.hostLabel_p2_eq_hostLabel_regionMerge_complement` |
| `TNLean.PEPS.threeBlockFiber_card` | none needed: twin is `ThreeBlockGeometry.threeBlockFiber_card` |
| `TNLean.PEPS.threeBlockDoubleSum_eq_smul_single` | none needed: twin is `ThreeBlockGeometry.threeBlockDoubleSum_eq_smul_single` |
| `TNLean.PEPS.threeBlockBlueCoeff` | none needed: twin is `ThreeBlockGeometry.threeBlockBlueCoeff`; all surviving receiver hits are geometry-native |
| `TNLean.PEPS.threeBlockDoubleSum_eq_blueCoeff_sum` | none needed: twin is `ThreeBlockGeometry.threeBlockDoubleSum_eq_blueCoeff_sum` |
| `TNLean.PEPS.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical` | none needed: twin is `ThreeBlockGeometry.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical` |
| `TNLean.PEPS.regionInteriorBondProd_smul_threeBlockComplWeight_eq` | none needed: twin is `ThreeBlockGeometry.regionInteriorBondProd_smul_threeBlockComplWeight_eq` |
| `TNLean.PEPS.regionBlockedWeight_threeBlockComplPhysical_mem_range` | none needed: the range-membership conclusion of the factorization chain; its only consumers were the endpoint inversions of the deleted continuation file |

## The surviving import edges

`UnionInjectivity.lean` previously imported the file for the three injectivity
lemmas alone; with them relocated, its import of `ThreeBlockResonate` is dropped
entirely rather than retargeted. The generated aggregator
`TNLean/PEPS/RegionBlock.lean` is regenerated and drops the module's import
line. No other module imported the file.

## Prose repointed

- The module docstring of `UnionInjectivity.lean` narrated the old in-file
  resonate route through `threeBlockComplPhysical` and
  `regionInteriorBondProd_smul_threeBlockComplWeight_eq`, which the current
  `toThreeBlockGeometry` delegation no longer uses. It now narrates the
  bare-geometry proof of `UnionInjectivityGeneral2` that the file actually
  packages, citing the same `ThreeBlockGeometry` lemmas the union lemma's own
  docstring cites.
- The docstring of `ThreeBlockGeometry.complCoeff_combination_eq_zero` in
  `UnionInjectivityGeneral2.lean` cited the deleted
  `threeBlockComplPhysical g σblue σcompl`; it now cites the surviving twin
  `g.complPhysical σblue σcompl`.
- The `filter_sum_split` candidate entry of `docs/tactic_patterns.md` loses its
  named site inside the removed file; the corrected count is three surviving
  occurrences.
- The `region_cover_union_cases` candidate entry of `docs/tactic_patterns.md`
  loses the three pattern blocks the file contributed (the survey's named site
  `ThreeBlockResonate.lean:97` plus two more inside its "+5"); the corrected
  count is five surviving occurrences, verified by a recount of the full
  three-line pattern signature.

## What is retained and what is deferred

`UnionInjectivity.lean` (now the home of the three injectivity lemmas) and
`ThreeBlockTransfer.lean` remain, both with live consumers; they are the last
two modules of the S3 route. The ledger entry S3 of
`docs/proof_debt_ledger.md` is updated, and the deferral paragraphs of
`docs/audits/2026-09-19_peps_regionblock_dead_closures.md` and
`docs/audits/2026-09-21_peps_three_block_resonate2.md` record this pass.

The removal qualifies for the no-deprecation path of
`docs/project_conventions.md`: no non-Archive use survives, no `\lean{}` tag
cites any removed name, and every removed declaration is named above with its
replacement.
