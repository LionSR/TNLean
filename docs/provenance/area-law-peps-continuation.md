# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
Last coordination check: October 7, 2026, 17:49 UTC.

## Verified mathematical contributions

| Contribution | Pull request | Exact verified source | Published evidence head |
|---|---|---|---|
| Fine-cell refinement and sparse-belt decay | [#8837](https://github.com/LionSR/TNLean/pull/8837) | `fc87534a119694461e9c3d3c37a7bfa1bf3ea960` | `4e12e35eb90436f776d998345950e70bfdce68b2` |
| Uniform separation of dyadic scales | [#8846](https://github.com/LionSR/TNLean/pull/8846) | `4be0ad6b5e6bc2d1523ba02b8675377c05549da5` | `44615152fb68de9bc913f491231dd7325f3fdef4` |
| Polynomial absorption and the numerical series bound | [#8848](https://github.com/LionSR/TNLean/pull/8848) | `5652d02446787ee2b9248db1057df48adbe32492` | `ed84770bf703478d69e4c8625d005c645d1a2529` |
| Primary birth regions, rectangular fragments and adjacent meshes | [#8851](https://github.com/LionSR/TNLean/pull/8851) | `d469be1a0a7799f4613e64e8139893b0fa2ee11d` | `fd8bf12587482c1db66c8c626a9df57cc4db025f` |

All 44 exact imported declarations in these four contributions have passing
canonical build and standard-axiom evidence. Their complete provenance
validation passes 205 entries. The four new counting rows remain planned
in the 209-entry continuation.
The detailed commands, logs, hashes and scope are recorded in
[fine belts](evidence/8758-fine-belts.md),
[scale separation](evidence/8758-scale-separation.md), and
[polynomial sums](evidence/8758-polynomial-budget.md), and
[primary regions](evidence/8758-primary-regions.md).
These proofs must not be rebuilt merely because work resumes.

At the last coordination check, all three contributions passed their full Lean
builds, compiled blueprint checks, rendering and module policies. The polynomial
draft's failed timing job had no diagnostic log; its failed-only rerun passed.
The fine-belt draft had two approvals on its exact published head. All three
drafts remained open and unmerged. Refresh external statuses before acting.

## Ownership and remaining mathematics

The geometric continuation is claimed under
[TNLean #8758](https://github.com/LionSR/TNLean/issues/8758).
Template and boundary estimates, entropy improvement, finite scanner iteration,
generic quantum-information results, and PEPS compression retain their existing
owners. Consult the live claims before extending or changing those interfaces.

The current [primary-region claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6042706326)
is on `feat/area-law-primary-regions`, following #8848. Its source draft is
[#8851](https://github.com/LionSR/TNLean/pull/8851). Its source contribution
contains four definitions and thirteen theorems in `PrimaryRegions.lean`,
`PrimaryFragments.lean` and `AdjacentScales.lean`. Direct elaboration with the
package options and independent mathematical review passed. The canonical
Geometry build passed in 11.746 seconds and the seventeen-name actual imported
audit passed in 4.266 seconds, at exact source
`d469be1a0a7799f4613e64e8139893b0fa2ee11d`. Only standard logical axioms occur.
The formatting-only head `8f060ee701641816520b394d8de198d3271dbe44` preserves
all Lean and audit bytes. The completed evidence is published at
`fd8bf12587482c1db66c8c626a9df57cc4db025f`.

The local whole-library blueprint check failed at a missing pre-existing
`TNLean.MPS.Examples.Fibonacci.olean` artifact. Its exact diagnostic is retained
separately from the successful theorem checks. Full CI supplies the compiled
whole-library blueprint check; inspect the current PR checks before claiming
that it passed. The source formatting failure was corrected with the repository
formatter and its idempotence verified.

The construction closes the intersection of an actual layer with an open pitch
interior. It gives the exact finite union of nonempty rectangular fragments,
fragment count `(2^(p-k)+2)^2` for `k ≤ p`, fragment diameter at most `2^k`,
whole-region diameter at most `2^p`, and same-layer separation at least `2^ℓ`.
The adjacent fine exponent increases by zero or one, giving side ratio one or
two. Empty layers and fragments are included. The closed-rectangle identity
explicitly requires a nonempty actual intersection, exactly as enforced by the
fragment index set. Half-open indexing cells are distinguished from open birth
interiors at arbitrary real boundary points.

The number of primary identifiers in an entire layer, contacts, isolated stars,
descendant estimates, simultaneous repairs, separation from earlier birth
regions, and the complete two-family partition remain open. The polynomial
series bound does not count actual repairs. The faithful area-law and polynomial
PEPS main theorems remain unproved.

The [whole-primary count](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6043238525)
is now claimed on `feat/area-law-primary-count`, in the source-only preparation
worktree. `PrimaryCounting.lean` now characterizes the actual nonempty pitch
intersections at arbitrary scales and proves `|primaries| ≤ 4|layer cells|`
for `k ≤ p`, then `|primaries| ≤ 32(2C₀+1)^2|boundary edges|`. Its four
proofs passed direct elaboration with all package options in 4.035 seconds,
without warnings, and independent mathematical review approved the precise
source scope. Canonical compilation and the imported four-name audit are
pending. The four new provenance rows remain planned. The next mathematical contribution is the actual nine-marks construction
for belt cells and its count at most nine times the belt-cell count, from
Section 11, lines 325–330. Confirm the live claims and publish its scope
before implementation. The mixed-scale affine mesh, point separation and
distance from nonincident axis or diagonal lines are subsequent prerequisites; full isolated-star geometry requires
actual fan regions and merged identifiers, with its straight-ray conclusion
proved rather than assumed.

## Worktrees and evidence preservation

- The warmed worktree `worktrees/area-law-peps-models` has completed the parent
  check and is available for the counting branch. Its package pins and cache
  are unchanged; the new counting target can reuse the parent Geometry artifacts.
- `worktrees/area-law-source-preparation` holds `feat/area-law-primary-count`,
  with the parent evidence merged. It has no Lake cache. Keep its source-only
  preparation separate from the canonical build; move the checked branch to
  the existing warmed worktree instead of seeding or rebuilding Mathlib.
- The parent canonical driver has finished and released the shared lock. Its
  build, axiom and failed blueprint logs are committed; do not repeat it.
- The hot-main worktree remains with the coordinating owner. Do not reset or
  interfere with an active peer worktree or change its dependency pins.

The next local action is to freeze the merged counting source, capture the
immutable 205-entry parent baseline, then build only the changed Geometry target
and import-audit its four declarations through the warmed worktree wrapper.
Promote only the new four rows after the actual checks pass. The known missing
whole-library cache artifact must not trigger a repeated local full build;
compiled blueprint checking is supplied by the separate full CI.

At the latest coordination check, the boundary comparisons were ready in
[#8849](https://github.com/LionSR/TNLean/pull/8849), and the analytic owner was
preparing separate quantum-information and entropy results. Their compressed
selected-vector construction is disjoint from the geometry assignment.
No model, entropy, scanner, QICLean, or PEPS-compression ownership is changed.

The published
[geometry handoff](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6042318628)
and
[tracker handoff](https://github.com/LionSR/TNLean/issues/8733#issuecomment-6042338516)
record the exact contribution boundaries. No main-branch merge or dependency-pin
change was performed by this contribution.
