# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
Last coordination check: October 7, 2026, 17:20:05 UTC.

## Verified mathematical contributions

| Contribution | Pull request | Exact verified source | Published evidence head |
|---|---|---|---|
| Fine-cell refinement and sparse-belt decay | [#8837](https://github.com/LionSR/TNLean/pull/8837) | `fc87534a119694461e9c3d3c37a7bfa1bf3ea960` | `4e12e35eb90436f776d998345950e70bfdce68b2` |
| Uniform separation of dyadic scales | [#8846](https://github.com/LionSR/TNLean/pull/8846) | `4be0ad6b5e6bc2d1523ba02b8675377c05549da5` | `44615152fb68de9bc913f491231dd7325f3fdef4` |
| Polynomial absorption and the numerical series bound | [#8848](https://github.com/LionSR/TNLean/pull/8848) | `5652d02446787ee2b9248db1057df48adbe32492` | `ed84770bf703478d69e4c8625d005c645d1a2529` |

All 27 exact imported declarations have passing canonical build and
standard-axiom evidence. The complete provenance validation passes 188 entries.
The detailed commands, logs, hashes and scope are recorded in
[fine belts](evidence/8758-fine-belts.md),
[scale separation](evidence/8758-scale-separation.md), and
[polynomial sums](evidence/8758-polynomial-budget.md).
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
Geometry build, seventeen-name imported audit and compiled blueprint check
are queued at proof source `d469be1a0a7799f4613e64e8139893b0fa2ee11d`. The published
head `8f060ee701641816520b394d8de198d3271dbe44` fixes required LaTeX formatting
only; every Lean and audit byte is identical. The
[source draft #8851](https://github.com/LionSR/TNLean/pull/8851) is published.
Its seventeen rows remain planned until their exact canonical logs pass.

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

- The warmed worktree `worktrees/area-law-peps-models` is on
  `feat/area-law-primary-regions`, based on `7d288086001edc540f46b0fe97b52863cc3bd310`.
  Its exact frozen head is `8f060ee701641816520b394d8de198d3271dbe44`,
  with Lean and audit bytes identical to the earlier proof source.
  Record the evidence head after the queued canonical checks pass.
- `worktrees/area-law-source-preparation` is on `feat/area-law-primary-count`,
  based on that parent formatting head. It has no Lake cache; no builds or
  cache seeding should run there. Nonmutating scratch elaboration uses the
  independent warmed worktree without changing its frozen source.
- The hot-main worktree is maintained by the coordinating owner. Inspect its
  activity and exact revision before using it; do not reset a peer's active
  worktree or seed from an incompletely warmed source.
- The previous local verification finished and released the shared lock.
  The primary-region check is queued without busy waiting. Its driver log is
  `/tmp/tnlean-8758-primary-regions-driver.log`; do not start a duplicate check.
  The frozen build and imported-audit logs will be saved under
  `docs/provenance/evidence/8758-primary-regions-*.log`.
  The entropy-dimension build belongs to another team; it was actively compiling
  at 17:18 UTC and has no completion estimate. No peer process was interrupted.
  The [boundary-owner coordination](https://github.com/LionSR/TNLean/issues/8759#issuecomment-6043017148)
  records the intended targeted check.

The published
[geometry handoff](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6042318628)
and
[tracker handoff](https://github.com/LionSR/TNLean/issues/8733#issuecomment-6042338516)
record the exact contribution boundaries. No main-branch merge or dependency-pin
change was performed by this contribution.
