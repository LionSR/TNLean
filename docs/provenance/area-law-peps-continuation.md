# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
Last coordination check: October 7, 2026, 18:07 UTC.

## Verified mathematical contributions

| Contribution | Pull request | Exact verified source | Published evidence head |
|---|---|---|---|
| Fine-cell refinement and sparse-belt decay | [#8837](https://github.com/LionSR/TNLean/pull/8837) | `fc87534a119694461e9c3d3c37a7bfa1bf3ea960` | `4e12e35eb90436f776d998345950e70bfdce68b2` |
| Uniform separation of dyadic scales | [#8846](https://github.com/LionSR/TNLean/pull/8846) | `4be0ad6b5e6bc2d1523ba02b8675377c05549da5` | `44615152fb68de9bc913f491231dd7325f3fdef4` |
| Polynomial absorption and the numerical series bound | [#8848](https://github.com/LionSR/TNLean/pull/8848) | `5652d02446787ee2b9248db1057df48adbe32492` | `ed84770bf703478d69e4c8625d005c645d1a2529` |
| Primary birth regions, rectangular fragments and adjacent meshes | [#8851](https://github.com/LionSR/TNLean/pull/8851) | `d469be1a0a7799f4613e64e8139893b0fa2ee11d` | `fd8bf12587482c1db66c8c626a9df57cc4db025f` |
| Number of actual primary identifiers | [#8856](https://github.com/LionSR/TNLean/pull/8856) | `b1dc393c764962cbc0cfb4c1bbefd3519c04a967` | `61fd819e7fe4689b8e0893affc9f127238b191ec` |

All 48 exact imported declarations in these five contributions have passing
canonical build and standard-axiom evidence. Complete provenance validation
passes 209 entries. The four counting rows alone were promoted in the latest
contribution; all previous 205 records and their evidence remain unchanged.
Commands, logs, hashes and mathematical scope are recorded in
[fine belts](evidence/8758-fine-belts.md),
[scale separation](evidence/8758-scale-separation.md),
[polynomial sums](evidence/8758-polynomial-budget.md),
[primary regions](evidence/8758-primary-regions.md), and
[primary counts](evidence/8758-primary-count.md).
These proofs must not be rebuilt merely because work resumes.

The first three drafts have passing full Lean builds, compiled blueprint
checks, rendering and module policies. The polynomial draft's failed timing
job had no diagnostic log; its failed-only rerun passed. The fine-belt draft
had two approvals on its exact published head. The parent #8851's latest full
CI and rendering remain in progress at the last read. Refresh external statuses
before acting; all drafts remain open and no main-branch merge was performed.

## Ownership and remaining mathematics

The geometric continuation is claimed under
[TNLean #8758](https://github.com/LionSR/TNLean/issues/8758).
Template and boundary estimates, entropy improvement, finite scanner iteration,
generic quantum-information results, and PEPS compression retain their existing
owners. Consult live claims before extending or changing those interfaces.

The [primary-region claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6042706326)
is on `feat/area-law-primary-regions`, following #8848. Its source contains
four definitions and thirteen theorems in `PrimaryRegions.lean`,
`PrimaryFragments.lean` and `AdjacentScales.lean`. The canonical Geometry build
passed in 11.746 seconds and the seventeen-name imported audit passed in
4.266 seconds at the exact source recorded above. The formatting-only head
`8f060ee701641816520b394d8de198d3271dbe44` preserves all Lean and audit bytes;
completed evidence is published at `fd8bf12587482c1db66c8c626a9df57cc4db025f`.

The parent local whole-library blueprint check failed at a missing pre-existing
`TNLean.MPS.Examples.Fibonacci.olean` artifact. Its exact diagnostic is retained
separately from the successful theorem checks. That unrelated whole-library
check was not repeated for the counting contribution. Full CI supplies the
compiled whole-library check; inspect current checks before claiming success.

The primary construction closes the intersection of an actual layer with an
open pitch interior. It gives the exact finite union of nonempty rectangular
fragments, fragment count `(2^(p-k)+2)^2` for `k ≤ p`, fragment diameter at most
`2^k`, whole-region diameter at most `2^p`, and same-layer separation at least
`2^ℓ`. The adjacent fine exponent increases by zero or one, giving side ratio
one or two. Empty layers and fragments are included. The rectangle identity
requires a nonempty actual intersection, exactly as enforced by the fragment
index set. Half-open indexing cells are distinguished from open birth interiors.

The [whole-primary count](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6043238525)
is on `feat/area-law-primary-count`. Its four declarations characterize the
actual nonempty pitch intersections at arbitrary scales and prove
`|primaries| ≤ 4|layer cells| ≤ 32(2C₀+1)^2|boundary edges|` for `k ≤ p`.
The canonical Geometry build passed in 16.557 seconds and the imported
four-name audit passed in 4.032 seconds at `b1dc393c764962cbc0cfb4c1bbefd3519c04a967`.
Only `propext`, `Classical.choice` and `Quot.sound` occur. Independent review,
package-option elaboration, blueprint source synchronization, prose checks,
formatter idempotence and complete 209-entry provenance validation passed.

The next [belt-mark claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6043892601)
is on `feat/area-law-belt-marks`, with source-only preparation in
`Geometry/BeltMarks.lean`. It constructs the center, corners and side midpoints
as actual points, proves cell-closure membership and the exact nine-point
count, then deduplicates the finite union over actual belt cells. The intended
uniform bound is at most nine times the belt-cell count and hence at most
`576(2C₀+1)^2|boundary edges|2^(-δ₀k/2)` for a selected sparse shift.
The six declarations have passed direct package-option elaboration without
warnings and independent mathematical review. Their canonical evidence remains
pending; the six new provenance rows remain planned in the 215-entry collection.
Source: Section 11, lines 325–330 of the pinned manuscript. The proof author
owns only the new Lean file; separate reviewers handle source and provenance.
The root agent owns imports, blueprint, canonical verification and publication.

Contacts, actual fans and merged identifiers, the minimum mark scale across
layers, isolated stars, descendant estimates, simultaneous repairs, separation
from earlier birth regions and the complete two-family partition remain open.
Mixed-scale affine-mesh point separation and distance from nonincident axis
or diagonal lines are the next independent prerequisites. The straight-ray
conclusion must be proved on actual tile regions. Polynomial summability does
not count actual repairs. Both source-faithful headline theorems remain unproved.

## Worktrees and evidence preservation

- `worktrees/area-law-peps-models` holds `feat/area-law-primary-count`. Its
  canonical counting driver has finished and released the shared lock. The
  existing warmed cache and all package pins remain unchanged.
- `worktrees/area-law-source-preparation` holds `feat/area-law-belt-marks`,
  initially based on the frozen counting source. It has no `.lake` directory.
  Merge the completed counting evidence before freezing the marks, then move
  the branch to the existing warmed worktree for one targeted canonical check.
- The prior canonical checks and logs must not be repeated. Never clear or
  reseed this warmed cache merely to prepare another auxiliary contribution.
- The hot-main worktree belongs to the coordinating owner. Do not reset an
  active peer worktree, interrupt its build or change dependency pins.

The next local action is to freeze the reviewed belt-mark source and perform
one targeted Geometry build and exact imported six-name audit in the warmed
worktree. The completed counting evidence and draft #8856 are published.
promote only the new rows when actual checks pass. Complete compiled blueprint
checking is supplied by full CI, preserving the known local artifact limitation.

At the latest coordination check, the boundary comparisons were ready in
[#8849](https://github.com/LionSR/TNLean/pull/8849); the analytic owner published
separate entropy/radius arithmetic in [#8854](https://github.com/LionSR/TNLean/pull/8854)
and quantum-information results in [QICLean #605](https://github.com/LionSR/QICLean/pull/605).
Their compressed selected-vector construction is disjoint from the geometry.
Template owners are testing current main `18a6dd4d` with QICLean `83fdc804`;
this geometric branch preserves its own verified pins until coordinated
integration. No model, entropy, scanner, QICLean or PEPS ownership is changed.

The earlier [geometry handoff](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6042318628)
and [tracker handoff](https://github.com/LionSR/TNLean/issues/8733#issuecomment-6042338516)
record previous contribution boundaries. No main-branch merge or dependency-pin
change was performed by this contribution.
