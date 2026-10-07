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
is on `feat/area-law-primary-regions`, following #8848. Its source contribution
contains four definitions and thirteen theorems in `PrimaryRegions.lean`,
`PrimaryFragments.lean` and `AdjacentScales.lean`. Direct elaboration with the
package options and independent mathematical review passed. The canonical
Geometry build passed in 11.746 seconds and its seventeen-name imported audit
passed in 4.266 seconds at exact source
`d469be1a0a7799f4613e64e8139893b0fa2ee11d`. All dependencies are standard
logical axioms. The seventeen rows have been canonically promoted. Source
draft [#8851](https://github.com/LionSR/TNLean/pull/8851) is published; its
formatting head `8f060ee701641816520b394d8de198d3271dbe44` preserves every
Lean and audit byte. The full local blueprint check stopped at a missing
pre-existing Fibonacci compiled artifact; the full CI supplies that check.

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

After canonical verification and publication, the next substantial geometric
obligation is a finite set of actual primary pitch indices, with a bound by a
universal constant times the layer-cell count. Check current ownership and
claim this precise continuation before implementation. The later nine-marks
construction must use actual belt cells; full isolated-star geometry requires
actual fan regions and merged identifiers, with its straight-ray conclusion
proved rather than assumed.

## Worktrees and evidence preservation

- The warmed worktree `worktrees/area-law-peps-models` is on
  `feat/area-law-primary-regions`, based on `7d288086001edc540f46b0fe97b52863cc3bd310`.
  Freeze its new source before canonical verification; record the exact source
  and evidence heads after the checks pass.
- `worktrees/area-law-source-preparation` holds the documentation preparation
  branch. It has no seeded Lake cache; no builds should run there.
- The hot-main worktree is maintained by the coordinating owner. Inspect its
  activity and exact revision before using it; do not reset a peer's active
  worktree or seed from an incompletely warmed source.
- The previous local verification finished and released the shared lock.
  The new primary-region check must use the same lock without busy waiting.
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
