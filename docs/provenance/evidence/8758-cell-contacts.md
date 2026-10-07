# Fine-cell contacts and dummy-neighborhood corners

Seven planned declarations classify positive-length contacts between actual
fine cells and locate contributing dummy-cell corners on their whole and
elementary sides.

Distinct indexed actual fine cells are disjoint as half-open sets, for all
natural radii and layer indices. Suppose that $C\ge2$, the reference index
$k\ge50{,}000{,}000$, and two distinct indexed actual fine cells have a closed
intersection containing two distinct points. Their fine exponents are equal
or differ by one. The intersection is a whole side of the smaller cell,
facing the opposite side of the larger cell. It is a whole side of both
cells when the exponents agree, and a midpoint half of the larger side
otherwise. The theorem requires no late bound on the opposing layer.
Its midpoint halves use the optional all-midpoint fan; matching under the
actual corner-induced mask is a later composition.

For $C\ge2$ and $k\ge k_0$, a corner of a contributing coarse cell in the
initial dummy neighborhood lying on a whole side of an actual fine cell
of layer $k$ is one of its endpoints. The same endpoint conclusion holds
on every optional elementary segment containing that corner. These two
assertions require no late-layer, endpoint-set nonemptiness or distinct-cell
hypothesis. Dummy-contact separation forces $k=k_0$; the corner and side
endpoints then belong to a common mesh whose spacing excludes a third
point on the side.

Two further assertions assign a point outside the initial neighborhood
to a unique actual half-open fine cell and express the full-plane cover by
that neighborhood and the actual fine cells at later or equal layers, for a
nonempty endpoint set and width at least two. Their
exact signatures and proofs have passed independent review.

These results classify two-cell contacts and exclude dummy corners in
elementary-side interiors. Exact matching under the actual subdivision mask,
constancy of the opposing primary or dummy region, global label assignment,
active rays, sectors and the complete isolated-star construction remain
further obligations.

## Source and original proofs

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.

The actual half-open layers appear in lines 173–181. Fine-cell sides and
contacts use `prop:two-families`, lines 299–306, and the local fine-mesh
argument at `geometry:initial-stars`, lines 352–356. Dummy corners use
lines 160–191, 200–207 and 299–310, including `geometry:layer-distance`.

The proofs are independently written with OpenAI Codex (GPT-6) assistance
under #8758; no upstream Lean source or proof text is reused. The successor
contribution was [publicly claimed before execution](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6046999707).
The fine-cell partition extension was [also claimed before execution](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6047068695).

## Frozen source and actual canonical evidence

Frozen source revision: **Pending**.

`TNLean/PEPS/AreaLaw/Geometry/CellContacts.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.dyadicCellSide`;
- `TNLean.PEPS.AreaLaw.Geometry.fineLayer_cells_disjoint`;
- `TNLean.PEPS.AreaLaw.Geometry.fineLayer_closedCell_contact`.

`TNLean/PEPS/AreaLaw/Geometry/DummyCorners.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_corner_on_side`;
- `TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_corner_on_elementarySide`.

`TNLean/PEPS/AreaLaw/Geometry/FineCellPartition.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.exists_unique_fineCell_of_not_mem_dyadicNeighborhood`;
- `TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_union_iUnion_fineCells_eq_univ`.

| Check | Actual command | Exit code | Elapsed seconds |
|---|---|---|---|
| Geometry target | `lake build TNLean.PEPS.AreaLaw.Geometry` | Pending | Pending |
| Imported seven-name audit | `lake env lean docs/provenance/evidence/8758-cell-contacts-axioms.lean` | Pending | Pending |

The released contact source passed direct package-option elaboration in
13.91 seconds without diagnostics. The released dummy-corner source passed
the same kind of check in 9.5196 seconds without diagnostics. Independent
mathematical review approved all seven exact signatures and proofs.
The released fine-cell partition source passed direct package-option
elaboration in 5.272664 seconds without diagnostics.
These direct source checks do not substitute for the pending canonical
build and imported audit at the final frozen revision.

Canonical verification must use the existing warmed worktree under the
shared repository lock and the pinned prebuilt Mathlib artifacts. The
source-only preparation worktree has no `.lake` directory and performs
no cache or build operation.

Evidence paths and SHA256 hashes:

- `docs/provenance/evidence/8758-cell-contacts-build.log`: **Pending**;
- `docs/provenance/evidence/8758-cell-contacts-axioms.log`: **Pending**.

Each completed log must record the exact command, frozen revision, elapsed
time and exit code. Only trailing whitespace may be normalized; actual
diagnostics and kernel reports must be retained.

## Provenance and integration

The completed parent is `9e4c09f446b5598229704ebe77688e848f4ae36d`, published
in [#8870](https://github.com/LionSR/TNLean/pull/8870), with 259 inventory
entries. All parent shard bytes, proof sources and historical evidence are
preserved. The existing planned root-ledger entry remains planned.

The seven new rows remain planned until exact-source canonical verification.
The strict helper checks all seven public declarations, original-proof
notices, imported audit names, source labels, licenses, command headers,
log hashes and the full 266-entry current-policy schema. Its immutable
259-row byte baseline is checked against the completed parent Git objects.
No parent row or verification record is replaced.

Strict static validation and promotion: **Pending**.
Complete blueprint source synchronization and changed-declaration coverage: **Pending**.
Formatter, prose and generated imports: **Pending**.

The historical local whole-library `leanblueprint checkdecls` failure from
a missing pre-existing `Fibonacci.olean` artifact remains preserved.
Full-library CI, compiled blueprint declaration checking and rendering
remain pending.
