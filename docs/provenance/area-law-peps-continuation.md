# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
Last coordination refresh: October 7, 2026, 21:02–21:07 UTC.
The goal remains active. Both source-faithful headline theorems remain unproved.

## Verified geometric contributions

| Contribution | Publication | Exact verified source | Evidence |
|---|---|---|---|
| Fine-cell refinement and sparse-belt decay | [#8837](https://github.com/LionSR/TNLean/pull/8837) | `fc87534a119694461e9c3d3c37a7bfa1bf3ea960` | [fine belts](evidence/8758-fine-belts.md) |
| Uniform separation of dyadic scales | [#8846](https://github.com/LionSR/TNLean/pull/8846) | `4be0ad6b5e6bc2d1523ba02b8675377c05549da5` | [scale separation](evidence/8758-scale-separation.md) |
| Polynomial absorption and series bound | [#8848](https://github.com/LionSR/TNLean/pull/8848) | `5652d02446787ee2b9248db1057df48adbe32492` | [polynomial sums](evidence/8758-polynomial-budget.md) |
| Actual primary regions, fragments and adjacent scales | [#8851](https://github.com/LionSR/TNLean/pull/8851) | `d469be1a0a7799f4613e64e8139893b0fa2ee11d` | [primary regions](evidence/8758-primary-regions.md) |
| Actual primary identifier count | [#8856](https://github.com/LionSR/TNLean/pull/8856) | `b1dc393c764962cbc0cfb4c1bbefd3519c04a967` | [primary counts](evidence/8758-primary-count.md) |
| Nine-point marks and sparse count | [#8857](https://github.com/LionSR/TNLean/pull/8857) | `0b1556b85180ed55e2a1db6ada9f44cc24a8df2b` | [belt marks](evidence/8758-belt-marks.md) |
| Quarter mesh and neighboring-layer locality | [#8859](https://github.com/LionSR/TNLean/pull/8859) | `5db13f626cbba4ce128e25ddcdb60a00532f0f3a` | [mesh and locality](evidence/8758-quarter-mesh.md) |
| Finite initial marks, minimum sides and separation | [#8862](https://github.com/LionSR/TNLean/pull/8862) | `5d2246bb32045fafea826200dd09b3518629ae97` | [initial marks](evidence/8758-initial-mark-family.md) |
| Actual fans, marked vertices and unique nonbelt primaries | [#8865](https://github.com/LionSR/TNLean/pull/8865) | `8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2` | [cell fans](evidence/8758-cell-fans.md) |
| Cyclic runs, opposing corners and half-open layer assignment | [#8867](https://github.com/LionSR/TNLean/pull/8867), evidence `41a653ac` | `778149a282158bbb92b4d7bb25fb12339d2f31ca` | [fan runs and layers](evidence/8758-fan-runs.md) |
| Actual side subdivisions and dummy contacts | `feat/area-law-actual-side-mask`, based on #8867 | `f8b62e1b56c8f7e356c870322aa3418702349a68` | [subdivisions and dummy contacts](evidence/8758-actual-side-mask.md) |

These eleven contributions contain 98 distinct verified declarations.
The current-policy collection has 259 rows; the old planned root row remains
planned. The latest eight rows have passing canonical build and imported
standard-axiom evidence. All 251 parent rows and every original evidence
artifact are preserved unchanged. Do not repeat successful canonical checks
merely because work resumes.

At the latest frozen source, the Geometry target passed in 59.834 seconds and
the imported eight-name audit in 30.477 seconds, without warnings. Only the
two new proof modules and the Geometry aggregator were compiled; pinned
Mathlib artifacts were reused. Complete source synchronization passes with
20,213 distinct public references and 20,207 flattened declaration records,
including eight new records in six mathematical environments and five checked
proof tags. Generated imports cover 2,845 production modules in 75 files.

The first seven geometric pull requests have passing full checks. #8862 has
passing Lean build and module checks, with blueprint rendering still running.
#8865 and #8867 have passing source/provenance checks and ongoing full CI.
The latest publication awaits its own full CI and rendering. Refresh statuses
before acting; local narrow verification is distinct from complete CI.

## Current mathematical scope and next action

The latest mask ranges over all actual fine cells at indices at least k₀,
including nonbelt cells. A side is divided exactly when its midpoint is an
actual opposing corner. Every such corner on a resulting elementary segment
is one of its endpoints. The reference layer alone has the threshold
50,000,000; the statement does not impose k≥k₀, an opposing late threshold,
a distinct-cell premise or a belt premise. Two public geometric lemmas give
the whole-side/midpoint-half endpoint cases and elementary-side containment
for every optional midpoint mask.

The closed neighborhood has an endpoint witness at distance at most
(C+1)2ᵏ. For k≥k₀+1, its distance from the closed layer Dₖ is at least
(C−1)2ᵏ₀, for every natural C. Thus for C≥2, a shared closure point with
k≥k₀ forces k=k₀. No late index or nonempty-endpoint-set premise is added.
These statements do not yet classify dummy corners or opposing identifiers.

The contact author retains the
[positive-length cell-contact claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6046503590)
in uncommitted `CellContacts.lean`. Actual half-open cell disjointness,
integer-offset classification and midpoint coordinates have passed narrow
checks. The final opposing-side conversion and assembled theorem remain under
verification. The intended conclusion is that a nontrivial closed intersection
of distinct actual cells is a whole side of the smaller cell, with opposite
side orientations and side ratio one or two. No contact certificate is assumed.

After publishing the current evidence, claim and prove the actual dummy-corner
step in a new module: a contributing coarse-neighborhood corner on a whole
reference fine side is an endpoint. Shared closure first forces k=k₀; all
points lie on the full fine mesh, and the two incident mesh-distance bounds
contradict the segment length unless the corner is an endpoint. Reuse the
public elementary-side lemmas for arbitrary optional midpoint masks. This step
has been scouted read-only and has no production claim or edits yet.

Then combine the exact corner-induced masks with the reviewed cell-contact
classification to prove reversed matching endpoints. Existence and constancy
of an opposing primary/dummy identifier on an **open** elementary segment are
separate obligations. Consistent global labels, active rays and sectors,
recursive repairs, descendant estimates, the full isolated-star lemma and
the complete two-family partition remain open. The initial-mark results
establish point separation only.

## Worktrees and verification discipline

- `worktrees/area-law-peps-models` owns `feat/area-law-actual-side-mask` and the
  group's only warmed cache. The canonical driver is finished and the shared
  lock released. Preserve the Lean, Mathlib and QICLean pins and all artifacts.
- `worktrees/area-law-source-preparation` is detached at `f8b62e1b` and has no
  `.lake`. Its untracked `CellContacts.lean` is active author work: preserve it
  when adopting completed evidence and creating the next source branch.
- Canonical builds and cache mutations use the worktree's own locked wrapper;
  the shared kernel lock waits without consuming CPU. Source elaboration uses
  the warm environment and package options. Never rebuild Mathlib from source
  or create a second warm cache for this group.
- Hot-main and dependency integration remain with their coordinating owner.
  Do not reset peer worktrees, interrupt peer builds, merge main or change pins.
- The earlier local whole-library declaration check failed at a missing
  pre-existing `Fibonacci.olean`. Its original log remains preserved; no repeat
  of that unrelated local full build is required.

## Other owners and coordination

Main remains `e3e3dddb429a61dd710ec9c8a3635ba6460ae222`. Template integration
#8798 (`077f62c33`) and boundary integration #8826 (`2ed6f6ed`) use model
`cd7271b9` and QICLean `83fdc804`. Their blueprint checks pass and Lean builds
are running. This geometric group retains verified QICLean `8d5389d2` until
coordinated adoption. Boundary #8849 (`b4168b0`) has all checks passing;
scanner #8834 (`d77854da`) has passing Lean/policy checks with blueprint
rendering running. Their native entropy conclusions remain separate.

The capped-partition owner retains #8863 at `b6f1f462`. Compatible warm review
proved the production target in 9.080 seconds. Strict regression failed in
11.971 seconds at missing documentation and concrete heartbeat/recursion
limits; strict audit exited 1 in 7.658 seconds at documentation/hash-command
linters. All 23 actual reports nevertheless satisfy the unchanged standard
axiom policy. Complete logs and corrections are attached in
[the review](https://github.com/LionSR/TNLean/pull/8863#issuecomment-6046537485)
and [coordination handoff](https://github.com/LionSR/TNLean/issues/8754#issuecomment-6046800493).
The owner must correct and recheck the diagnostic files; the verified production
proof need not be repeated. No peer source, ledger, cache or pin was changed.

Compression owns #8864/#8866/#8868. Latest joint-contraction source is
`c80913b10d9926f31004705c78f136ade6b8b466`, evidence #8868 at `28bc131e`.
Actual owner coarsening, selective source preparation and chronological gate
expansion preserving exterior contractions remain under #8769. QICLean #571
is open at `0d031f25`, with all six checks passing; its integration contact
remains requested. No geometry proof assumes the pending source-contraction
integration or establishes the full circuit error theorem.

The analytic group owns QICLean #618 generic Schur mass, #621 uniform Bell
occurrence/matching, #622 physical replica gap/cutoff/sectors, independent-copy
concentration and permutation covariance. It has claimed actual iid/Schur
entropy-compatible sector selection under #8753. Good-copy factorization,
native Hamiltonian tail and the complete high-label sequence remain separate.
The geometry group confirmed no overlap in
[public coordination](https://github.com/LionSR/TNLean/issues/8753#issuecomment-6046799993).
No competing analytic model or dependency adoption is introduced.

Check coordination approximately every thirty minutes and before each new
claim or shared-interface change. Direct cross-thread replies are unavailable
in this session; public issue coordination is authorized. Use a small team
with disjoint proof ownership. Continue the active goal without routine
permission requests and report unfinished mathematics accurately.
