# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
Last coordination check: October 7, 2026, 19:59 UTC.

## Verified mathematical contributions

| Contribution | Pull request or publication branch | Exact verified source | Evidence |
|---|---|---|---|
| Fine-cell refinement and sparse-belt decay | [#8837](https://github.com/LionSR/TNLean/pull/8837) | `fc87534a119694461e9c3d3c37a7bfa1bf3ea960` | [fine belts](evidence/8758-fine-belts.md) |
| Uniform separation of dyadic scales | [#8846](https://github.com/LionSR/TNLean/pull/8846) | `4be0ad6b5e6bc2d1523ba02b8675377c05549da5` | [scale separation](evidence/8758-scale-separation.md) |
| Polynomial absorption and numerical series bound | [#8848](https://github.com/LionSR/TNLean/pull/8848) | `5652d02446787ee2b9248db1057df48adbe32492` | [polynomial sums](evidence/8758-polynomial-budget.md) |
| Actual primary birth regions, fragments and adjacent scales | [#8851](https://github.com/LionSR/TNLean/pull/8851) | `d469be1a0a7799f4613e64e8139893b0fa2ee11d` | [primary regions](evidence/8758-primary-regions.md) |
| Number of actual primary identifiers | [#8856](https://github.com/LionSR/TNLean/pull/8856) | `b1dc393c764962cbc0cfb4c1bbefd3519c04a967` | [primary counts](evidence/8758-primary-count.md) |
| Actual nine-point marks and their sparse count | [#8857](https://github.com/LionSR/TNLean/pull/8857) | `0b1556b85180ed55e2a1db6ada9f44cc24a8df2b` | [belt marks](evidence/8758-belt-marks.md) |
| Quarter mesh and neighboring-layer locality | [#8859](https://github.com/LionSR/TNLean/pull/8859) | `5db13f626cbba4ce128e25ddcdb60a00532f0f3a` | [mesh and locality](evidence/8758-quarter-mesh.md) |
| Actual finite initial marks, minimum sides and separation | [#8862](https://github.com/LionSR/TNLean/pull/8862) | `5d2246bb32045fafea826200dd09b3518629ae97` | [initial mark family](evidence/8758-initial-mark-family.md) |
| Actual cell fans, marked vertices and unique nonbelt primaries | `feat/area-law-cell-fans`, based on #8862 | `8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2` | [cell fans](evidence/8758-cell-fans.md) |

All 76 exact imported declarations in these nine contributions have passing
canonical build and standard-axiom evidence. Complete current-policy provenance
validation passes 237 entries. Only the twelve fan/primary rows are promoted in
the latest contribution; all prior 225 records remain byte-identical. The old
planned root-ledger row remains planned. The exact commands, timings, hashes,
source anchors and scope limitations are in the evidence notes above.
Do not repeat these builds merely because work resumes.

The first seven pull requests have all checks passing, including the full Lean
build, compiled blueprint declaration checks, rendering and module policies.
The polynomial timing check passed its failed-only rerun. #8862 remains in full
CI at the last inspection. Full CI and rendering for the fan contribution are
pending publication. Refresh external statuses before acting. No main-branch
merge or dependency-pin change was performed.

## Current mathematical scope and next action

The [cell-fan claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6045048500),
[nonbelt-primary extension](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6045170965)
and [marked-vertex connection](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6045372605)
are complete. `CellFans.lean` constructs the actual dyadic-cell center and
perimeter segment endpoints. Every side is intact or divided at its midpoint.
The resulting four to eight actual triangles cover the closed cell; every
pairwise intersection is the center together with its radial joins to the
common perimeter segment points. Equal positions are included. The center
and every endpoint belong to the actual nine-point cell-mark set.

`NonbeltPrimaries.lean` identifies the shifted pitch index by integer division.
For aligned scales and an actual fine-layer cell omitted by both selected belt
residue classes, the closed cell lies in the birth region of a unique occupied
primary pitch index. Negative indices and touching sides are included; no
endpoint-set nonemptiness or hypothesis k ≤ p is added.

The combined Geometry build passed in 17.803 seconds at `8d3f5cd9`; the exact
imported twelve-name audit passed in 6.257 seconds. The position abbreviation
uses no axioms, the pitch-index definition uses `propext` only, and the other
ten names use only `propext`, `Classical.choice` and `Quot.sound`. All twelve
signatures and eight mathematical blueprint entries passed independent review.
Complete source synchronization passes 20,191 distinct public references and
20,185 flattened declaration records, including the twelve new records and
six checked proof tags. Reverse coverage, formatter idempotence and imports
pass. Preserve the exact Lean and imported-audit bytes from `8d3f5cd9`.

Next, publish this completed evidence contribution. Two agents are scouting,
without production edits, the actual opposing-cell side subdivision and the
subsequent cyclic merging of equal-color fan triangles. Inspect the source and
live claims, choose and publicly claim a concrete next obligation before writing
it. Derive side subdivision from actual layer membership and dyadic alignment;
do not assume a subdivision or merging certificate in place of that proof.

Consistent colors across actual shared sides, dummy interfaces, merged region
identifiers, active rays and sectors, the full isolated-star lemma, recursive
replacements, descendant estimates and the complete two-family partition remain
open. The initial-mark contribution establishes only the point-separation
assertion of the initial-star lemma: actual marks have an attained positive
smallest incident side and distinct marks have distance at least one quarter
of the larger such side. Both source-faithful headline theorems remain unproved.

## Worktrees and verification discipline

- `worktrees/area-law-peps-models` holds `feat/area-law-cell-fans` and the only
  warmed cache owned by this group. The canonical driver has finished and
  released the shared repository lock. Preserve all pins and cached artifacts.
- `worktrees/area-law-source-preparation` is detached at the frozen source
  `8d3f5cd9` and has no `.lake` directory. Merge completed evidence into the next
  source branch before freezing another contribution; preserve the 237-row
  parent baseline. Perform no cache, seed or build operation there.
- Canonical builds and cache mutations run through the worktree's own
  `scripts/lake_build_locked.sh`. The temporary driver uses the shared kernel
  lock; waiting consumes no CPU. Nonmutating source elaboration uses the warmed
  environment and package options. Never rebuild Mathlib from source.
- Hot-main belongs to the coordinating owner. Do not reset an active peer
  worktree, interrupt its build or change dependency pins without coordination.
- The old local whole-library blueprint check failed at a missing pre-existing
  `Fibonacci.olean`; its primary-region diagnostic remains intact. Do not repeat
  that unrelated local build. The earlier contributions have full compiled-book
  CI evidence; newer contributions await their own CI results.

## Other owners and coordination

Main is `e3e3dddb429a61dd710ec9c8a3635ba6460ae222`, including whole-group PEPS
truncation #8799 and dyadic routing #8796. Template and boundary integration
#8798 (`077f62c33`) and #8826 (`2ed6f6ed`) consume model `cd7271b9` and main
with QICLean `83fdc804`; the preceding combined boundary head passed full CI.
The geometric continuation preserves its already verified pins until coordinated
integration. The geometric template, safe-entropy and scanner work retain their
existing owners. Boundary comparison #8849 and scanner #8834 have all checks
passing; their native entropy conclusions remain separate obligations.

The capped-partition owner retains #8863 at `2b639859`. Read-only assistance
checked equality of its toolchain, pins and recursive imported source graph
with this group's warmed environment. Exact-source elaboration exposed one
implicit-cap error and an unused simp argument. A temporary copy with explicit
`(n := K)` in `Nat.findGreatest_is_greatest` and the unused argument removed
passes package-option elaboration without warnings. The
[verified correction](https://github.com/LionSR/TNLean/pull/8863#issuecomment-6045767900)
is compiler feedback only: no peer source, branch, cache or provenance changed.
Canonical production, regression and imported-axiom checks remain with its owner.

The compression group owns #8853/#8858/#8860, actual common branch spaces and
finite coordinate supports, and the next actual source-density coefficient
identity under [#8769](https://github.com/LionSR/TNLean/issues/8769#issuecomment-6045416169).
Its common-space proofs are compiled and final verification is underway. QICLean
#571 is open at `0d031f2518cfe0cc39a055454f2b5109926c1abc`, with all checks
passing; integration remains with its owner. Geometry does not own compression,
source-gate density, sampling, corrected-position estimates or lifetime bounds.

The analytic group owns TNLean #8854, selected-vector and typical-state results,
QICLean #605/#606/#608/#609/#610/#611, and Bell powers #614. Auxiliary-pair
entropy and literal spectral-cutoff mass proofs are being verified. The actual
common auxiliary label and native physical mean-energy bound remain within the
broad #8753 assignment and await explicit scope reconciliation before new edits.
The native Hamiltonian tail, coherent pins and amplification arguments remain
separate. No analytic or QICLean ownership is changed.

Check public coordination about every thirty minutes and before a new claim
or shared-interface change. Incoming cross-thread messages may be read, but
there is currently no callable tool for replying directly to those threads;
use the public issue coordination already authorized by the user. Keep a small
team with disjoint source ownership. Continue the active goal without routine
permission requests, and state outstanding mathematics accurately.
