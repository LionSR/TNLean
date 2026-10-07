# Cyclic fan runs, opposing corners and the half-open layer partition

Fourteen new declarations describe three parts of the dyadic construction:
merging consecutive triangles of a cell fan with equal labels, locating an
opposing fine-cell corner on a reference side, and partitioning the plane
by the actual half-open layers. Four existing declarations are also
reverified after a repeated cell-containment argument was replaced by a
single theorem. The mathematical statements of these four declarations are
unchanged.

## Mathematical content

For an actual square cell, each side is either intact or divided at its
midpoint. The fan positions index its four to eight actual triangles. Give
these positions arbitrary labels in a two-element set. Join two distinct
positions when an actual segment end is the other segment's start and the
labels agree. A run is a connected component of this graph; its region is
the union of its actual closed triangles.

The label is constant on a run. The run regions cover precisely the closed
cell. Consecutive positions in different runs have different labels. If all
positions have one label, their component identifiers agree and every run
region is the whole closed cell. Connectivity around the actual perimeter
is proved from the four sides and their optional midpoint divisions; it is
not assumed.

For a common origin, finite endpoint set and radius $C\ge2$, let $k$ be a
reference layer with $k\ge50{,}000{,}000$. Take an actual fine cell in that
layer and an actual fine cell in any layer $h$. If a corner of the latter
cell lies on a whole side of the former, it is that side's start, midpoint
or end. There is no additional lower bound on $h$, distinct-cell hypothesis
or belt hypothesis. Both actual fine-layer index memberships are required.
The whole side uses the unsplit fan endpoints.

Write $N_k$ for the existing dyadic neighborhood and
$D_k=N_{k+1}\setminus N_k$ for its actual half-open layer. The layers are
pairwise disjoint, and $N_{k_0}$ is disjoint from each $D_k$ with $k\ge k_0$,
for arbitrary finite endpoint set and natural radius. If the endpoint set
is nonempty and $C\ge2$, every point outside $N_{k_0}$ belongs to a unique
$D_k$ with $k\ge k_0$, and

$$
N_{k_0}\cup\bigcup_{k\ge k_0}D_k=\mathbb R^2.
$$

Indeed, the least neighborhood index $K$ containing such a point satisfies
$K>k_0$; the point lies in $D_{K-1}$ and $K-1\ge k_0$. These statements
concern the half-open sets; their closures may meet. The shared containment
theorem says that every actually indexed dyadic cell of exponent
$\ell\le k$ is contained in $D_k$, for arbitrary endpoint set and radius.

## Source, attribution and scope

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, pinned at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.

The run construction is in lines 313–318 of the proof of `prop:two-families`.
The opposing-corner subdivision is in lines 299–306 and the local-scale
argument in lines 352–356 at `geometry:initial-stars`. Neighborhood nesting,
exhaustion and the actual layer definition occur in lines 160–177; the
shared finer-cell containment also uses lines 154–160 and 173–181.

The labels in a single cell remain arbitrary. Consistent opposite labels
across distinct cells, the global choice of side divisions, active rays and
sectors, the full isolated-star statement, recursive replacements and the
complete two-family partition remain separate obligations. These results
do not establish either manuscript headline theorem.

The proofs are independently written; no upstream Lean source or proof text
is reused. OpenAI Codex (GPT-6) assists LionSR under the claims for
[fan runs](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6045812354),
[opposing corners](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6045875781),
[half-open layers](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6045925148),
and the [shared containment theorem](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6045994088).

## Exact inventory and canonical evidence

Exact verified source: `778149a282158bbb92b4d7bb25fb12339d2f31ca`.

`TNLean/PEPS/AreaLaw/Geometry/FanRuns.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.cellFanRunGraph`;
- `TNLean.PEPS.AreaLaw.Geometry.CellFanRun`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFanRunRegion`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFanRun_color_eq`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFanRunRegions_cover`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFanRun_adjacent_colors_ne`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFanRun_all_equal`.

`TNLean/PEPS/AreaLaw/Geometry/SideSubdivision.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.dyadicCellCorner`;
- `TNLean.PEPS.AreaLaw.Geometry.fineLayer_corner_on_side`.

`TNLean/PEPS/AreaLaw/Geometry/LayerPartition.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices`;
- `TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_pairwiseDisjoint`;
- `TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_disjoint_later_layer`;
- `TNLean.PEPS.AreaLaw.Geometry.exists_unique_layer_of_not_mem_dyadicNeighborhood`;
- `TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_union_iUnion_layers_eq_univ`.

The combined imported audit also includes the four existing declarations
listed in the retention table below, giving eighteen exact reports.

| Check | Actual command | Exit code | Elapsed seconds |
|---|---|---|---|
| Combined Geometry target | `lake build TNLean.PEPS.AreaLaw.Geometry` | 0 | 22.002 |
| Imported eighteen-name audit | `lake env lean docs/provenance/evidence/8758-fan-runs-axioms.lean` | 0 | 4.327 |

Canonical verification ran at the exact source above from the existing
warmed worktree under the shared repository lock, through
`scripts/lake_build_locked.sh --`, reusing the pinned prebuilt Mathlib
artifacts. The final Geometry build and imported audit completed without
warnings. The build compiled `LayerPartition` in 6.1 seconds,
`FineMarkSeparation` in 6.0 seconds, `NonbeltPrimaries` in 6.3 seconds,
`SideSubdivision` in 7.4 seconds, `InitialMarkFamily` in 3.6 seconds and
the Geometry aggregator in 3.1 seconds. The unchanged `FanRuns` artifact
was reused from the first check recorded below.

The imported reports contain precisely the eighteen names above.
Seventeen depend only on `propext`, `Classical.choice` and `Quot.sound`;
`nonbeltPitchIndex` depends only on `propext`.

The source-only preparation worktree had no `.lake` directory and performed
no cache or build operation. Combined non-mutating elaboration with the
package options passed in 14.570 seconds without warnings. Independent
reviews approved the three modules, their blueprint statements and the
containment replacements. Read-only comparison also confirmed that the
four reverified public statements agree with their original exact sources.

Evidence paths and SHA256 hashes:

- `docs/provenance/evidence/8758-fan-runs-build.log`: `74ccf580ada01969f925e758e88b1487b36595776fd15cd51debae92675222be`;
- `docs/provenance/evidence/8758-fan-runs-axioms.log`: `113d15edf7e8bd9786a17dbbf84ae29fcaa7c6391741bfadc27e889485cdc567`.

Each actual log records its exact command, frozen revision, exit code and
elapsed time. Only trailing whitespace was normalized; the actual diagnostics
and quoted axiom reports are preserved.

## Retention of prior verification

The immutable parent is `9688dda9c3c79fe37f4fac2b556788a9932d20ee`, which
contains the original 237-entry inventory. Its ledger bytes remain available
in Git. Precisely four entries require new verification because the current
policy checks the complete source file against its recorded revision, and
the containment abstraction changes two previously verified files.

| Declaration | Original exact source | Preserved evidence note |
|---|---|---|
| `fineLayer_marks_dist_ge` | `5d2246bb32045fafea826200dd09b3518629ae97` | `docs/provenance/evidence/8758-initial-mark-family.md` |
| `nonbeltPitchIndex` | `8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2` | `docs/provenance/evidence/8758-cell-fans.md` |
| `closure_nonbeltCell_subset_primaryBirthRegion` | `8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2` | `docs/provenance/evidence/8758-cell-fans.md` |
| `exists_unique_primary_of_nonbeltCell` | `8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2` | `docs/provenance/evidence/8758-cell-fans.md` |

Their identities, mathematical source mappings, license, notices, status and
original change descriptions are retained. A new description records the
abstraction and points to the original verification; only the required
verification records are replaced by the actual canonical evidence above. The
original build and axiom logs and their evidence notes are preserved.
The other 233 prior entries remain byte-equivalent to the parent,
including the previously existing planned root-ledger entry.

## Provenance and integration

Strict static promotion passed for the fourteen new rows in
`docs/provenance/openai-math.d/8758-fan-runs.json` and replacement of the
four required prior verification records in `8758-initial-mark-family.json`
and `8758-cell-fans.json`. The complete 251-entry current-policy
provenance/source/license/notice audit passed, including exact source and
committed audit bytes, command headers, all eighteen imported reports and
actual evidence hashes. All 233 other entries agree with the immutable
parent. The schema and validation policy were not changed.

The entry-level baseline was captured from the immutable Git parent itself.
Static preparation projected only the four affected entries to pending in
memory; completed promotion uses their actual new verification records.
The original notes, imported audits and log hashes remain unchanged.

Complete blueprint source synchronization and reverse coverage passed:
20,205 distinct public references and 20,199 flattened theorem-like
records, with `sync_ok: true` and no missing, stale or duplicate references.
The fourteen new declaration records occur in twelve mathematical
environments and have ten checked proof tags. No changed declaration is
missing its blueprint entry.

Formatter idempotence, reader-facing prose and generated import checks
passed; 75 generated files cover 2,843 production modules. All three modules
and their mathematical blueprint statements passed independent review.
The repeated half-open cell-containment argument was recorded in the tactic
ledger and promoted to the common theorem; its three local copies were
replaced. Previously recorded pattern decisions remain unchanged.

The earlier primary-region contribution recorded a local whole-library
`leanblueprint checkdecls` failure caused by a missing pre-existing
`Fibonacci.olean` artifact. That historical failure log remains intact.
Full-library CI, compiled blueprint declaration checking and rendering
remain pending. Publication branch: `feat/area-law-fan-runs`, stacked on #8865. The pull request is created after the completed evidence commit; no main-branch merge is performed.

## First canonical check and notice correction

The first canonical check at `89c5cd185dd5b14a3ae9b33c8a1a1cfa6c4f561f`
passed Geometry compilation in 20.473 seconds and the eighteen imported axiom
reports in 4.852 seconds. It reported one long-line warning on the shared
containment lemma's machine-readable provenance identifier. The new identifier
was shortened before publication; no declaration or proof changed. The original
successful commands and actual warning remain in `8758-fan-runs-first-build.log`
and `8758-fan-runs-first-axioms.log`. The corrected source received the fresh canonical verification recorded
above; no record was promoted at the first revision.

The preserved first-check log hashes are:

- `8758-fan-runs-first-build.log`: `c7a05fe2394735426ff055c81de50fac44dcd5a5b6545ba28dd8864bcd3acd2a`;
- `8758-fan-runs-first-axioms.log`: `9853b14436c84f44cd1b3e220cd273e4fbc73b26c4bf4b2df823ae9d4fbcbca7`.
