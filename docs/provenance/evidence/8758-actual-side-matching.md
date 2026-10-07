# Actual elementary-side matching and common side endpoints

This contribution is prospective. Its three new declarations remain planned;
no final source revision, canonical build or imported kernel report is yet recorded.
The five declarations whose source files are being refactored retain their
historical verification until new exact-source evidence is available.

## Mathematical scope

The two common endpoint theorems concern the unsplit counterclockwise sides of
an actual translated dyadic square. For every origin, natural scale, integer
cell index and side index, they give the exact coordinates of the start and
end, and identify these endpoints with actual corners of the same square.
Neither theorem has an additional hypothesis.

The proposed matching theorem assumes a common origin and layer data,
`C ≥ 2`, a reference layer `k ≥ 50000000`, `k₀ ≤ k`, `k₀ ≤ h`, actual
fine-cell membership at both layers, and distinct indexed cells. A segment
of the reference cell under the exact actual midpoint mask is assumed to
have contact containing two distinct points with the other closed cell.
The conclusion supplies a segment under that cell's exact actual mask,
with the opposite facing side index and reversed endpoint equalities.
Only the reference layer has the late-layer assumption. The released
signature and proof will be reviewed before these statements are recorded
as verified.

This matching statement is conditional on contact. Opponent existence,
opponent uniqueness, consistent region labels, rays, sectors, subsequent
repairs, descendants, isolated stars and the global two-family partition
remain separate obligations. Neither headline area-law theorem is claimed.

## Manuscript and independence

- Manuscript: OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11.
- Immutable source revision:
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- Source path:
  `preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
- Source passages: lines 299–306 for the side subdivisions and common
  endpoint statements, and lines 352–356 for the scale-ratio argument.
- Source labels: `prop:two-families` and `geometry:initial-stars`.
- All three new records describe original formalizations from mathematical
  manuscript statements; no upstream Lean proof text is reused. The common
  coordinate proof is extracted from TNLean's already independently proved
  cell-contact argument. OpenAI Codex (GPT-6) assistance is disclosed.

## New declaration inventory

All names are in `TNLean.PEPS.AreaLaw.Geometry`.

| Module | New theorem | State |
| --- | --- | --- |
| `SideEndpoints.lean` | `cellFan_unsplit_endpoints_coordinates` | Planned; release and verification pending |
| `SideEndpoints.lean` | `cellFan_unsplit_endpoints_are_corners` | Planned; release and verification pending |
| `ActualSideMatching.lean` | `fineLayer_elementary_contact_match` | Planned; release and verification pending |

## Exact-source verification

Frozen source revision: **pending**.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Pending | Pending | Pending |
| Imported eight-name audit | `lake env lean docs/provenance/evidence/8758-actual-side-matching-axioms.lean` | Pending | Pending | Pending |

The canonical commands are to be executed by the coordinating agent under
the existing shared repository lock in the already warmed worktree. This
metadata preparation executes no Lean or Lake command. No source or cache
check is represented as completed here.

Independent mathematical review, complete source synchronization and reverse
coverage, generated imports, formatting and prose checks are pending for
this contribution. Full CI and rendering are also pending. The earlier
whole-library local blueprint check failed because the pre-existing
`TNLean/MPS/Examples/Fibonacci.olean` was absent; its log and limitation
remain preserved. A narrow geometry build does not establish a complete
compiled blueprint check.

## Retention of the prior exact-source evidence

Completed parent: `863405980e1ebca928f76bb883ed794d2fc32e5a`, PR
[8876](https://github.com/LionSR/TNLean/pull/8876).
The parent collection contains 266 entries. This contribution adds three
entries, for 269 in total, and reverifies precisely five existing entries.
All 261 other entries and every unaffected shard remain unchanged.

The five statements below retain their public signatures, source mappings,
identities, licenses and notices. The shared endpoint proofs are extracted
to `SideEndpoints.lean`, changing the containing source files. The policy
requires verification against those new complete file bytes. On a successful
canonical check, only a reverification explanation is appended and the
verification record is updated for these five entries.

| Existing declaration | Original source revision | Retained evidence |
| --- | --- | --- |
| `dyadicCellSide` | `0ac139a04b8d2519f1199bfe8e2f78a5f1fd63c2` | `8758-cell-contacts.md` and its build/kernel logs |
| `fineLayer_cells_disjoint` | `0ac139a04b8d2519f1199bfe8e2f78a5f1fd63c2` | Same historical note and logs |
| `fineLayer_closedCell_contact` | `0ac139a04b8d2519f1199bfe8e2f78a5f1fd63c2` | Same historical note and logs |
| `dyadicNeighborhood_corner_on_side` | `0ac139a04b8d2519f1199bfe8e2f78a5f1fd63c2` | Same historical note and logs |
| `dyadicNeighborhood_corner_on_elementarySide` | `0ac139a04b8d2519f1199bfe8e2f78a5f1fd63c2` | Same historical note and logs |

The original ledger bytes remain in Git at the completed parent. The
immutable baseline records the parent shards, each entry and 47 historical
evidence files, including the original cell-contact note and imported audit.
The strict helper checks this retention before it permits temporary outputs.
No parent entry is overwritten by this prospective preparation.
