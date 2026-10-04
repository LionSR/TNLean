# PEPS three-block injectivity: retire the edge-centred factorization

This is the fourth slice of ledger S3, implementing #7902 after #7875.
At base `be3ddcfd1`, `ThreeBlockResonate.lean` contains 874 lines and 23
declarations. Only the following three have live code consumers outside the
module; their statements, proofs and docstrings move verbatim to
`UnionInjectivity.lean`:

- `TNLean.PEPS.regionBlockedTensorInjective_red`: seven call sites across
  `NormalAbsorbedFamily`, `NormalEdgeGaugeFamily`, `NormalGeneralFundamentalTheorem`,
  `NormalSquareEdgeCoeff`, and `RegionBlock/ThreeBlockTransfer`.
- `TNLean.PEPS.regionBlockedTensorInjective_blue`: the union theorem.
- `TNLean.PEPS.regionBlockedTensorInjective_complement`: the union theorem.

## Consumer and blueprint checks

Each of the 23 names was searched separately with fixed-string matching across
`TNLean`, `blueprint/src`, `scripts`, and `docs/paper-gaps`. Receivers and
namespace-qualified names were inspected to distinguish the general partition
results from the deleted edge-centred results. The blueprint tag census,
including comma-separated and continued tags, contains none of these exact
fully qualified names. The tagged `regionBlockedTensorInjective_union` remains
unchanged. There is no mathematical statement change.

The only handwritten import is `UnionInjectivity.lean`; it now imports
`NormalEdgeBlockingData` and `RegionBlock/UnionClosure` explicitly alongside
the existing general union result. Generated aggregators are regenerated.
The three deleted simp lemmas have no surviving explicit reference; the root
full-root build remains required to verify that no remaining proof uses them implicitly.

## Removed declarations and replacements

These names are removed without compatibility aliases under the repository's
public-API policy. All general replacements below are declared in
`UnionInjectivityGeneral.lean`.

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.threeBlockComplPhysical` | `TNLean.PEPS.ThreeBlockGeometry.complPhysical` |
| `TNLean.PEPS.threeBlockComplPhysical_apply_blue` | `TNLean.PEPS.ThreeBlockGeometry.complPhysical_apply_blue` |
| `TNLean.PEPS.threeBlockComplPhysical_apply_not_blue` | `TNLean.PEPS.ThreeBlockGeometry.complPhysical_apply_not_blue` |
| `TNLean.PEPS.sdiff_red_eq_blue_union_complement` | `TNLean.PEPS.ThreeBlockGeometry.sdiff_red_eq_blue_union_complement` |
| `TNLean.PEPS.prod_sdiff_red_eq_blue_mul_complement` | `TNLean.PEPS.ThreeBlockGeometry.prod_sdiff_red_eq_blue_mul_complement` |
| `TNLean.PEPS.regionBlockedWeight_threeBlockComplPhysical_eq` | `TNLean.PEPS.ThreeBlockGeometry.regionBlockedWeight_complPhysical_eq` |
| `TNLean.PEPS.isRegionBoundaryEdge_red_edge` | No replacement needed: unused step of the removed edge-centred argument. |
| `TNLean.PEPS.redBoundaryEdge` | No replacement needed: unused step of the removed edge-centred argument. |
| `TNLean.PEPS.redBoundaryEdge_coe` | No replacement needed: unused step of the removed edge-centred argument. |
| `TNLean.PEPS.threeBlockInsertedCoeff` | No replacement needed: unused step of the removed edge-centred argument. |
| `TNLean.PEPS.threeBlockInsertedCoeff_eq_regionInsertedCoeff` | No replacement needed: unused step of the removed edge-centred argument. |
| `TNLean.PEPS.blueProd_eq_regionMerge_complement` | `TNLean.PEPS.ThreeBlockGeometry.blueProd_eq_regionMerge_complement` |
| `TNLean.PEPS.hostLabel_p2_eq_hostLabel_regionMerge_complement` | `TNLean.PEPS.ThreeBlockGeometry.hostLabel_p2_eq_hostLabel_regionMerge_complement` |
| `TNLean.PEPS.threeBlockFiber_card` | `TNLean.PEPS.ThreeBlockGeometry.threeBlockFiber_card` |
| `TNLean.PEPS.threeBlockDoubleSum_eq_smul_single` | `TNLean.PEPS.ThreeBlockGeometry.threeBlockDoubleSum_eq_smul_single` |
| `TNLean.PEPS.threeBlockBlueCoeff` | `TNLean.PEPS.ThreeBlockGeometry.threeBlockBlueCoeff` |
| `TNLean.PEPS.threeBlockDoubleSum_eq_blueCoeff_sum` | `TNLean.PEPS.ThreeBlockGeometry.threeBlockDoubleSum_eq_blueCoeff_sum` |
| `TNLean.PEPS.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical` | `TNLean.PEPS.ThreeBlockGeometry.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical` |
| `TNLean.PEPS.regionInteriorBondProd_smul_threeBlockComplWeight_eq` | `TNLean.PEPS.ThreeBlockGeometry.regionInteriorBondProd_smul_threeBlockComplWeight_eq` |
| `TNLean.PEPS.regionBlockedWeight_threeBlockComplPhysical_mem_range` | No replacement needed: unused step of the removed edge-centred argument. |

## Documentation

The union module's explanation now names `ThreeBlockGeometry.complPhysical`
and its general factorization. Two further stale explanatory names in
`UnionInjectivityGeneral` and `UnionInjectivityGeneral2` now cite their live
geometry versions. The tactic-pattern ledger points only at surviving sites;
the filter-sum pattern has two verified sites. Historical audit notes remain
historical, with the architectural survey and S3 updated to record this slice.

## Validation

- `lake exe cache get`: all 8,943 prebuilt Mathlib artifacts downloaded;
  `Mathlib.olean` verified before building. Mathlib was not compiled from source.
- `lake build TNLean.PEPS.RegionBlock.UnionInjectivity`: passed with the package
  linter options at source commit `1d82af581` (1,975 jobs including dependencies).
- The three moved theorem, proof and docstring blocks are byte-identical; each
  name has exactly one declaration and no deleted module import survives.
- Import aggregation, forbidden-token, reader-facing prose, numbered-file,
  oversized-file and whitespace checks passed.
- Full-root verification is pending PR CI; the focused build alone does not
  establish that the deleted attributes have no downstream use.
