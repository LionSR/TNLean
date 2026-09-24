# PEPS union injectivity: the dead namespaced blue mirror blocks

`TNLean/PEPS/RegionBlock/UnionInjectivityGeneralBlue.lean` carried five
`ThreeBlockGeometry`-namespaced blue-side lemmas derived from the complement-side
results through the `swapBlueComplement` involution, and
`TNLean/PEPS/RegionBlock/UnionInjectivityGeneral.lean` carried the function-level
form of the complement-side smul-factorization. None of the six declarations had a
consumer anywhere in the tree: every match on the five blue names outside their own
declarations was either the unnamespaced twin of the edge-centred resonate route
(`ThreeBlockResonate2.lean`, itself deleted in the third S3 slice) or a docstring
mention, and the function-level complement form was cited only by prose. The
2026-09-21 round-two architectural simplification survey (candidate E3) verified the
blocks dead, and they are deleted rather than documented. None carried a `sorry` or
an `axiom`, and no Blueprint `\lean{...}` tag cites any of the six.

## Removed declarations and their replacements

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.ThreeBlockGeometry.complProd_eq_regionMerge_blue` | none needed: no consumer. It is a one-line application of the complement-side `blueProd_eq_regionMerge_complement` through `swapBlueComplement`, and re-derives as such if a blue-side consumer ever appears |
| `TNLean.PEPS.ThreeBlockGeometry.hostLabel_p2_eq_hostLabel_regionMerge_blue` | none needed: no consumer; one line through `swapBlueComplement` as above |
| `TNLean.PEPS.ThreeBlockGeometry.threeBlockBlueFiber_card` | none needed: no consumer; one line through `swapBlueComplement` as above |
| `TNLean.PEPS.ThreeBlockGeometry.threeBlockDoubleSum_eq_smul_single_blue` | none needed: no consumer; one line through `swapBlueComplement` as above |
| `TNLean.PEPS.ThreeBlockGeometry.threeBlockDoubleSum_eq_complCoeff_sum_blue` | none needed: no consumer; one line through `swapBlueComplement` as above |
| `TNLean.PEPS.ThreeBlockGeometry.regionInteriorBondProd_smul_threeBlockComplWeight_eq` (`UnionInjectivityGeneral.lean`) | none needed: the union proof strips the blue block first and consumes the blue function-level form `regionInteriorBondProd_smul_geometryBlueWeight_eq` (`UnionInjectivityGeneralBlue.lean`), never the complement-first order this theorem served |

## What was checked before the deletion

Each of the six final name components was searched across `TNLean`, `blueprint`,
`docs` and `scripts`, and every match was attributed by the namespace in scope at
its site. The namespaced forms had no consumer; the capstone
`regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue` proves
itself by `swapBlueComplement_complPhysical` together with the complement-side
pointwise factorization, bypassing all five deleted blue lemmas. The forty-odd
consumers behind the shared short names resolve to the survivors
`threeBlockComplCoeff` and the two capstones (in `UnionInjectivityGeneral2`,
`OverlapSetup`, `OverlapBridge` and the torus window chain), not to the deleted
five. The declaration-tag inventory contains no `\lean{...}` citation of any of the
six.

## Prose repointed

- The module docstring of `TNLean/PEPS/RegionBlock/UnionInjectivity.lean` described
  the retired complement-first order through the deleted
  `regionInteriorBondProd_smul_threeBlockComplWeight_eq`. It now describes the proof
  as written: the annihilation is read at the fused blue/complement leg, the blue
  smul-factorization `regionInteriorBondProd_smul_geometryBlueWeight_eq` rewrites it
  as a blue-block combination, injectivity of the blue block strips the blue part,
  and injectivity of the complement block finishes.
- The module header of `UnionInjectivityGeneralBlue.lean` announced the file as the
  blue-side mirror of the complement-side factorization; it now names the surviving
  pointwise capstone and its function-level form.
- `docs/audits/2026-09-21_peps_three_block_resonate2.md` credited the forty-odd
  consumers to all seven `ThreeBlockGeometry` twins and listed five of the deleted
  names as the replacements for its removed unnamespaced declarations. The
  attribution sentence and the five affected rows are corrected there: the
  consumers belong to `threeBlockComplCoeff` and the capstone alone, and the five
  twins were as consumer-free as the declarations they replaced.
- The S3 entry of `docs/proof_debt_ledger.md` records this follow-up.

## What is retained and what is deferred

Retained: the involution `swapBlueComplement` with its three `@[simp]` projections
and `swapBlueComplement_complPhysical` (used by the capstone), the complement
coupling coefficient `threeBlockComplCoeff`, the pointwise capstone
`regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue` and
its function-level form `regionInteriorBondProd_smul_geometryBlueWeight_eq`, and
the unnamespaced twin
`regionInteriorBondProd_smul_threeBlockComplWeight_eq` of
`ThreeBlockResonate.lean`, which that file itself consumes.

Deferred: after this deletion the three `@[simp]` rfl projections
`swapBlueComplement_red`, `swapBlueComplement_blue` and
`swapBlueComplement_complement` have no named consumer. As projections of an
abbrev they may still fire silently inside `simp`, so they are left to a
build-checked batch rather than deleted here.

The removal qualifies for the no-deprecation path of
`docs/project_conventions.md`: no non-Archive use survives, no `\lean{}` tag cites
any removed name, and every removed declaration is named above with its
replacement.
