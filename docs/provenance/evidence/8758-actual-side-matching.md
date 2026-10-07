# Actual elementary-side matching, opponents and common side endpoints

All four new declarations and the five unchanged prior statements have passed
exact-source canonical verification and independent mathematical review.
The original prior evidence remains preserved.

## Mathematical scope

The two common endpoint theorems concern the unsplit counterclockwise sides of
an actual translated dyadic square. For every origin, natural scale, integer
cell index and side index, they give the exact coordinates of the start and
end, and identify these endpoints with actual corners of the same square.
Neither theorem has an additional hypothesis.

The matching theorem assumes a common origin and layer data,
`C ≥ 2`, a reference layer `k ≥ 50000000`, `k₀ ≤ k`, `k₀ ≤ h`, actual
fine-cell membership at both layers, and distinct indexed cells. A segment
of the reference cell under the exact actual midpoint mask is assumed to
have contact containing two distinct points with the other closed cell.
The conclusion supplies a segment under that cell's exact actual mask,
with the opposite facing side index and reversed endpoint equalities.
Only the reference layer has the late-layer assumption. The released
signature and proof have passed independent mathematical review and exact-source
canonical verification.

The matching statement is conditional on contact. A separate theorem
provides an opponent for every actual elementary segment: under C ≥ 2,
k ≥ 50000000, k₀ ≤ k and actual reference membership, its entire closed
segment lies in the closure of the initial dummy neighborhood or in one
actual distinct closed fine cell at some h ≥ k₀. Nonemptiness of Z is
derived; no contact or plane-cover certificate, label or sparsity premise
is supplied. The finite outward cover and corner exclusion establish
whole-segment containment. Opponent uniqueness, consistent region labels,
rays, sectors, subsequent repairs, descendants, isolated stars and the global
two-family partition remain separate obligations. Neither headline area-law theorem is claimed.

## Manuscript and independence

- Manuscript: OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11.
- Immutable source revision:
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- Source path:
  `preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
- Source passages: lines 154–181 for the actual layer cover, lines
  299–310 for side subdivisions, common endpoints and opponents, and
  lines 352–356 for the scale-ratio argument.
- Source labels: `prop:two-families` and `geometry:initial-stars`.
- All four new records describe original formalizations from mathematical
  manuscript statements; no upstream Lean proof text is reused. The common
  coordinate proof is extracted from TNLean's already independently proved
  cell-contact argument. OpenAI Codex (GPT-6) assistance is disclosed.

## New declaration inventory

All names are in `TNLean.PEPS.AreaLaw.Geometry`.

| Module | New theorem | State |
| --- | --- | --- |
| `SideEndpoints.lean` | `cellFan_unsplit_endpoints_coordinates` | Verified at the exact source below |
| `SideEndpoints.lean` | `cellFan_unsplit_endpoints_are_corners` | Verified at the exact source below |
| `ActualSideMatching.lean` | `fineLayer_elementary_contact_match` | Verified at the exact source below |
| `ElementarySideOpponents.lean` | `exists_elementarySide_opponent` | Verified at the exact source below |

## Exact-source verification

Frozen source revision: `93c807b97f45312bab807ba47abb06f11d686f18`.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Passed, exit 0 | 35.475 s | `2b7fd47586ea1bf7da6c571cf3be91e3bce16020f84e0d56ff73fdab564e763b` |
| Imported nine-name audit | `lake env lean docs/provenance/evidence/8758-actual-side-matching-axioms.lean` | Passed, exit 0 | 4.101 s | `aff033950f86160e42250ecfd19672fdc60a2f87552127cf3d10a612cca946cf` |

The actual command headers, source revision, elapsed times, exit codes and
complete output are recorded in [the build log](8758-actual-side-matching-build.log)
and [the imported kernel log](8758-actual-side-matching-axioms.log). All nine
reports use only standard Lean logical axioms, and neither command reports
a warning. The commands ran through the worktree's own wrapper under the
shared repository lock. Waiting used no CPU. The prebuilt Mathlib cache
and existing TNLean artifacts were retained; only the three new proof modules,
two refactored callers and their aggregator compiled. No fresh cache, full
package build, Mathlib source build or dependency-pin change occurred.

The matching author reported a clean combined package-option source
elaboration of the four endpoint/matching/contact/corner modules in
59.46 seconds (user 28.29 seconds, system 15.55 seconds). The opponent
author reported a clean complete source check with the common endpoint
module in 56.63 seconds (user 7.45 seconds, system 14.54 seconds).
Independent review confirms all four new statements,
the five unchanged old signatures and preservation of the promoted
coordinate statement and proof. This source check precedes final notice
insertion and does not replace frozen-source canonical evidence.

The three new chapters and their router inputs pass pinned idempotent formatting.
They contain three mathematical theorem environments, four declaration records
and three proof tags, with all mathematical dependencies present. Complete
source synchronization passes with 20,224 distinct public references and 20,218
flattened declaration records, no missing or stale references, and full reverse
coverage for the changed declarations. Generated imports cover 2,851 production
modules in 75 files; prose, forbidden-token, numbered-module and file-length
policies pass. Independent readers approved every new statement and proof,
the five unchanged signatures and exact preservation of the promoted coordinate
proof. The scoped tactic scan and shared-lemma promotion are recorded in
[the pattern ledger](../../tactic_patterns.md). Full CI and compiled whole-book
checking are separate. The inherited contact chapter received a one-line
notation correction for ChkTeX Warning 44, at parent fix
`3da5bcf7053423f16162ad98e126379082d63dff`. The exact Ubuntu 1.7.8 PCRE pattern
matches the original half-open interval product and has no match after using
the standard left-bracket macro, or in any of the three new chapters. The
mathematical content and declaration tags are unchanged. Local ChkTeX 1.7.9
uses POSIX regex and does not reproduce the original CI warning; remote
whole-book success is still pending. The earlier
whole-library local blueprint check failed because the pre-existing
`TNLean/MPS/Examples/Fibonacci.olean` was absent; its log and limitation
remain preserved. A narrow geometry build does not establish a complete
compiled blueprint check.

## Retention of the prior exact-source evidence

Completed parent: `863405980e1ebca928f76bb883ed794d2fc32e5a`, PR
[8876](https://github.com/LionSR/TNLean/pull/8876).
The parent collection contains 266 entries. This contribution adds four
entries, for 270 in total, and reverifies precisely five existing entries.
All 261 other entries and every unaffected shard remain unchanged.

The five statements below retain their public signatures, source mappings,
identities, licenses and notices. The shared endpoint proofs are extracted
to `SideEndpoints.lean`, changing the containing source files. The policy
requires verification against those new complete file bytes. Only a reverification
explanation is appended and the verification record is updated for these
five entries after the successful canonical checks.

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
The unchanged normal provenance policy passes the complete 270-row collection.
The coordinating helper promoted the four new records and updated only the
five permitted old verification records and appended explanations.
It checked all 261 other rows and all 47 historical evidence files against
the immutable completed parent. Every frozen production, audit and blueprint
file remains byte-identical after recording this evidence.
