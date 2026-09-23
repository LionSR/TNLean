# PEPS RegionBlock: the three-block resonate continuation file

`TNLean/PEPS/RegionBlock/ThreeBlockResonate2.lean` (709 lines, fifteen
declarations) is removed in full. It was the middle-strip and endpoint-inversion
continuation of the edge-centred three-block resonate engine, the route the
proof-debt ledger records under S3 as a specialization of the source's
union-injectivity lemma rather than the lemma itself: it fixes a distinguished
edge through a `NormalEdgeBlockingData` where arXiv:1804.04964, Section 3 works
over an arbitrary partition. The general partition route
`UnionInjectivityGeneral*` proves the source statement over a bare
`ThreeBlockGeometry` and recovers this one as a special case. The file carried no
`sorry` and no `axiom`.

The 2026-09-19 closure audit
(`docs/audits/2026-09-19_peps_regionblock_dead_closures.md`) deleted
`ThreeBlockReconcile.lean`, the file's last consumer, and deferred this deletion
to a separate pass. That pass is this one.

## What was checked before the deletion

Every one of the fifteen declaration names was searched across `TNLean`, `docs`,
`blueprint` and `scripts`, and each external match was attributed by the
namespace in scope at its declaration site. Seven of the names are declared a
second time in the tree as `ThreeBlockGeometry`-namespaced members of
`UnionInjectivityGeneralBlue.lean`, and the forty-odd consumers of those names
all resolve to the namespaced member through dot notation on a geometry:
`complProd_eq_regionMerge_blue`, `hostLabel_p2_eq_hostLabel_regionMerge_blue`,
`threeBlockBlueFiber_card`, `threeBlockDoubleSum_eq_smul_single_blue`,
`threeBlockComplCoeff`, `threeBlockDoubleSum_eq_complCoeff_sum_blue` and
`regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue`.
The remaining eight names have no match at all outside the file except two prose
pointers, corrected below. No removed name carries an attribute or an instance
declaration.

No Blueprint `\lean{...}` tag cites a removed name. The Blueprint occurrence of
`threeBlockComplCoeff`, in
`blueprint/src/chapter/ch24_peps_ft_torus_single_bond_peeling.tex` (line 344),
is part of the compound name
`TNLean.PEPS.ThreeBlockGeometry.threeBlockBlueCoeff_eq_swap_threeBlockComplCoeff`,
which tags a different surviving declaration, so `checkdecls` is unaffected.

## Removed declarations and their replacements

The seven names with a `ThreeBlockGeometry` twin are replaced by that twin,
which states the same identity over a bare geometry instead of an
edge-centred blocking datum.

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.complProd_eq_regionMerge_blue` | `TNLean.PEPS.ThreeBlockGeometry.complProd_eq_regionMerge_blue` (`UnionInjectivityGeneralBlue.lean`) |
| `TNLean.PEPS.hostLabel_p2_eq_hostLabel_regionMerge_blue` | `TNLean.PEPS.ThreeBlockGeometry.hostLabel_p2_eq_hostLabel_regionMerge_blue` (same file) |
| `TNLean.PEPS.threeBlockBlueFiber_card` | `TNLean.PEPS.ThreeBlockGeometry.threeBlockBlueFiber_card` (same file) |
| `TNLean.PEPS.threeBlockDoubleSum_eq_smul_single_blue` | `TNLean.PEPS.ThreeBlockGeometry.threeBlockDoubleSum_eq_smul_single_blue` (same file) |
| `TNLean.PEPS.threeBlockComplCoeff` | `TNLean.PEPS.ThreeBlockGeometry.threeBlockComplCoeff` (same file) |
| `TNLean.PEPS.threeBlockDoubleSum_eq_complCoeff_sum_blue` | `TNLean.PEPS.ThreeBlockGeometry.threeBlockDoubleSum_eq_complCoeff_sum_blue` (same file) |
| `TNLean.PEPS.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue` | `TNLean.PEPS.ThreeBlockGeometry.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue` (same file) |
| `TNLean.PEPS.regionInteriorBondProd_smul_threeBlockBlueWeight_eq` | `TNLean.PEPS.regionInteriorBondProd_smul_geometryBlueWeight_eq` (same file), the geometry-native form of the same blue smul-factorization and the form the overlapping-descent bridge actually calls |
| `TNLean.PEPS.threeBlockComplRow` | none needed: the explicit preimage witness of the complement row, a proof step of the stripped middle |
| `TNLean.PEPS.regionInteriorBondProd_smul_threeBlockInsertedCoeff_eq` | none needed: the complement-row read-off feeding the middle strip |
| `TNLean.PEPS.threeBlock_middle_strip` | none needed: the middle-strip step of the edge-centred engine, whose consumer was the deleted reconcile file; the general route reaches union injectivity without a middle-strip step |
| `TNLean.PEPS.regionBlockedWeight_threeBlockBluePhysical_mem_range` | none needed: the range membership derived from the blue smul-factorization, used only by the two endpoint inversions |
| `TNLean.PEPS.regionInteriorBondProd_smul_threeBlockBlueWeight_eq_blockedMap` | none needed: the same identity phrased through the blocked-region tensor map, used only by the two endpoint inversions |
| `TNLean.PEPS.threeBlock_invert_blue` | none needed: the blue endpoint inversion, whose consumer was the deleted reconcile file |
| `TNLean.PEPS.threeBlock_invert_red` | none needed: the red endpoint inversion, whose consumer was the deleted reconcile file |

## The last import edge

`TNLean/PEPS/RegionBlock/UnionInjectivity.lean` was the only handwritten
importer besides the generated aggregator. Its proofs name no declaration of the
removed file: the two names it takes from that import cone,
`regionBlockedTensorInjective_blue` and
`regionBlockedTensorInjective_complement`, are declared one module earlier in
`ThreeBlockResonate.lean`, and the factorization its module docstring describes,
`regionInteriorBondProd_smul_threeBlockComplWeight_eq`, is declared there as
well. The import line is therefore retargeted at `ThreeBlockResonate` directly,
a one-for-one replacement. The generated aggregator
`TNLean/PEPS/RegionBlock.lean` is regenerated.

## Prose repointed

- `docs/paper-gaps/peps_normal_ft_section3_route.tex` cites the removed blue
  smul-factorization twice, in the description of the re-insertion bridge and in
  the statement of the landed right-geometry rebuild step. Both citations move
  to the geometry-native `regionInteriorBondProd_smul_geometryBlueWeight_eq`.
  That form states the same factorization over a bare geometry, and it is the
  one the cited rebuild step
  `overlapRight_bondProd_smul_hostWeight_combination_eq_zero` calls, so the
  corrected sentences are also more accurate than the ones they replace: both
  passages speak of the right geometry, not of an edge-centred blocking datum.
- The module docstring of `TNLean/PEPS/RegionBlock/ThreeBlockResonate.lean`
  named the removed middle-strip step when explaining why a third separately
  invertible block is needed. The explanation is kept and the pointer to the
  removed declaration dropped.
- The `filter_sum_split` candidate entry of `docs/tactic_patterns.md` cited one
  of its occurrences inside the removed file. The entry now cites three verified
  surviving sites and the corrected count of four occurrences.
- The removed path is dropped from the numbered-sequel debt allowlist of
  `scripts/check_numbered_lean_files.py`, as that ratchet requires for a deleted
  file.

## What is retained and what is deferred

`TNLean/PEPS/RegionBlock/ThreeBlockResonate.lean` is retained: it declares the
region-blocking associativity factorization and the two blocked-tensor
injectivity facts that `UnionInjectivity.lean` consumes. The remaining S3
candidates named in `docs/proof_debt_ledger.md`, the resonate file itself and
`UnionInjectivity.lean`, `ThreeBlockTransfer.lean`, still have live consumers and
are not touched here.

The removal qualifies for the no-deprecation path of
`docs/project_conventions.md`: no non-Archive use survives, no `\lean{}` tag
cites any removed name, and every removed declaration is named above with its
replacement.
