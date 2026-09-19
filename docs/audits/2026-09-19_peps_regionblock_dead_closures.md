# PEPS RegionBlock dead closures: the three-block reconcile file and the coarse post-capstone seam

Two independent closures under `TNLean/PEPS/RegionBlock/` had no consumer
anywhere in the production corpus at the audited head: no other declaration, no
Blueprint `\lean{...}` tag, no attribute, no instance. Both are the residue of
routes whose capstones landed without them, so they are deleted rather than
documented. Neither file carried a `sorry` or an `axiom`.

## The three-block reconcile file

`TNLean/PEPS/RegionBlock/ThreeBlockReconcile.lean` (371 lines, nine
declarations) is removed in full. It was the `V = W` reconcile step of the
edge-centred three-block resonate engine, the route the proof-debt ledger
records under S3 as a specialization of the source's union-injectivity lemma
rather than the lemma itself: it fixes a distinguished edge with a positivity
side condition that arXiv:1804.04964, Section 3 does not impose, and the general
partition route `UnionInjectivityGeneral*` already proves the source statement
and recovers this one as a special case.

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.threeBlock_reconcile` | `TNLean.PEPS.bondLocal_iff_coeffTransfer` (`TNLean/PEPS/RegionBlock/ThreeBlockTransfer.lean`), which delivers the source's `V = W` step over an arbitrary partition through `UnionInjectivityGeneral*` and fixes no distinguished edge |
| `TNLean.PEPS.threeBlockInsertedCoeff_eq_iff_regionInsertedCoeff_eq` | none needed: it existed only to read the reconcile's hypothesis as the three-block resonate equality |
| `TNLean.PEPS.threeBlock_middle_strip_descent` | none needed: a proof step of the reconcile |
| `TNLean.PEPS.threeBlock_red_readoff_eq_of_coeff_eq` | none needed: a proof step of the reconcile |
| `TNLean.PEPS.threeBlock_blue_readoff` | none needed: a proof step of the reconcile |
| `TNLean.PEPS.threeBlockBlueSplit` | none needed: a splitting helper of the two read-offs |
| `TNLean.PEPS.threeBlockComplSplit` | none needed: a splitting helper of the two read-offs |
| `TNLean.PEPS.threeBlockComplPhysical_split` | none needed: a splitting helper of the two read-offs |
| `TNLean.PEPS.regionInsertedCoeff_eq_threeBlockInsertedCoeff_split` | none needed: a splitting helper of the two read-offs |

The file became importer-free when the unused-import sweep recorded in
`docs/audits/2026-08-27_unused_import_lines.md` removed the
`ThreeBlockTransfer` import edge; the generated aggregator
`TNLean/PEPS/RegionBlock.lean` was its only remaining importer and is
regenerated. Two prose pointers are corrected: the module docstring of
`TNLean/PEPS/RegionBlock/ThreeBlockTransfer.lean` no longer claims to wire in
the deleted engine, since that file wires only the host-block union injectivity
and the two-block backbone; and the `region_cover_union_cases` candidate entry
of `docs/tactic_patterns.md` now cites a surviving site and the corrected count
of eight occurrences.

## The coarse three-site post-capstone seam

`TNLean/PEPS/RegionBlock/CoarseThreeSiteMul.lean` (121 lines, one theorem) is
removed in full, together with four further lemmas of the coarse three-site
chain. The chain's capstone `exists_regionEdgeGauge_of_coherentFrames`
(`CoarseThreeSite11.lean`) and the route feeding
`exists_regionEdgeGauge_of_blockingData` are untouched and keep their consumers.

| Removed declaration | File | Replacement |
|---|---|---|
| `TNLean.PEPS.coeffTransferMap_mul_of_coherentFrames` | `TNLean/PEPS/RegionBlock/CoarseThreeSiteMul.lean` | `coeffTransferMap_eq_regionEdgeTransfer` followed by `regionEdgeTransfer_mul` (both `CoarseThreeSite11.lean`), which is verbatim the removed proof |
| `TNLean.PEPS.isBondLocalTransferKernel_of_coherentFrames` | `TNLean/PEPS/RegionBlock/CoarseThreeSite11.lean` | `bondLocal_iff_coeffTransfer` (`ThreeBlockTransfer.lean`) composed with `exists_regionInsertedCoeff_eq_sharedRegion` (`CoarseThreeSite11.lean`) |
| `TNLean.PEPS.redBundleInsertedCoeff_add` | `TNLean/PEPS/RegionBlock/CoarseThreeSite6.lean` | `redBundleInsertedCoeff_singleton` (`CoarseThreeSite8.lean`) and `redBundleInsertedCoeff_bondModelMatrix_eq_configSum` (`CoarseThreeSite10.lean`), the forms the live single-edge route reads |
| `TNLean.PEPS.redBundleInsertedCoeff_smul` | `TNLean/PEPS/RegionBlock/CoarseThreeSite6.lean` | the same pair |
| `TNLean.PEPS.sameAwayFromRBBundle_hostMerge` | `TNLean/PEPS/RegionBlock/CoarseThreeSite9.lean` | `sameAwayFromRBBundle_regionBoundaryLabel_iff` (`CoarseThreeSite9.lean`), whose reverse direction repeats the same red, blue and complement case analysis and is the form the route uses |

The standalone multiplicativity theorem was a three-rewrite consequence of two
retained lemmas, and both are still called inside the capstone, so no content is
lost with it. The single-region coefficient transfers
`exists_regionInsertedCoeff_eq_sharedRegion` and its symmetric twin keep their
consumers inside the capstone. `bondLocal_iff_coeffTransfer` keeps its consumers
in `ThreeBlockTransfer.lean` and `TorusWindowBondLocal.lean`. The sibling
`redBoundaryRBCrossing_hostMerge` is used by `relaxedTriple_summand_eq` and is
retained; the section header above it is shortened to the one lemma it still
introduces.

## Paper-gap prose repointed

Neither closure carried a Blueprint tag, so no `\lean{}` payload or `\leanok`
changes. Eight narrative references in the paper-gap notes are repointed at the
survivors:

- `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the subsection presenting the
  reusable multiplicativity, now presents the capstone and names the retained
  identification and multiplication lemmas as the step that supplies it. The
  auditability claim it makes is unchanged: the overlapping-window route's
  multiplicativity is one application of that pair with the red region taken to
  be the window, and the unmet hypothesis is still the frame's complement
  injectivity, the documented obstruction. The footnote naming the coherent-frame
  mechanism as a conditional alternative now names the capstone.
- `docs/paper-gaps/peps_normal_ft_section3_route.tex` now describes the
  whole-bundle inserted coefficient through the single-crossing read-off and its
  configuration-sum expansion instead of its additivity and homogeneity; drops
  the deleted host-merge agreement lemma from the merged-summand sentence while
  keeping the two lemmas that step actually uses, and names the surviving
  characterization of the away-from-crossing label agreement; and cites
  `bondLocal_iff_coeffTransfer` for the two bond-local transfer kernels in both
  places where the deleted wrapper was named.

The section3 sentence on the merged summand previously listed the deleted
host-merge agreement lemma among the identifications used by
`relaxedTriple_summand_eq`. That proof never called it, so the corrected
sentence is also more accurate than the one it replaces.

## What is retained and what is deferred

`TNLean/PEPS/RegionBlock/ThreeBlockResonate2.lean` is retained here and deferred
to a separate pass. The reconcile file was its last consumer, so after this
deletion none of its fifteen declarations has a reference in code outside the
file: every external match on those names is either a distinct
`ThreeBlockGeometry`-namespaced declaration of `UnionInjectivityGeneralBlue` and
`UnionInjectivityGeneral2` that happens to share the short name — including
`threeBlockComplCoeff`, which is defined twice in the tree, once unnamespaced
here and once as `ThreeBlockGeometry.threeBlockComplCoeff` — or a docstring
mention. `UnionInjectivity.lean` still imports the module but uses only the
namespaced general forms. The deferred slice is therefore the whole file, not
the closure of about 250 to 300 lines an earlier count suggested; whether its
import edge from `UnionInjectivity.lean` can also go is a question for that
pass. It touches a paper-gap citation of `threeBlock_middle_strip` in
`docs/paper-gaps/peps_normal_ft_section3_route.tex` and a docstring pointer in
`ThreeBlockResonate.lean`, and is recorded as the next S3 step in
`docs/proof_debt_ledger.md`.

The removals qualify for the no-deprecation path of `docs/project_conventions.md`:
no non-Archive use survives, no `\lean{}` tag cites any removed name, and every
removed declaration is named here with its replacement.
