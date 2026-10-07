# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
Last coordination refresh: October 7, 2026, 21:29–21:38 UTC.
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
| Actual side subdivisions and dummy contacts | [#8870](https://github.com/LionSR/TNLean/pull/8870) | `f8b62e1b56c8f7e356c870322aa3418702349a68` | [subdivisions and dummy contacts](evidence/8758-actual-side-mask.md) |
| Fine-cell contacts, dummy corners and exact fine-cell assignment | `feat/area-law-cell-contacts`, based on #8870 | `0ac139a04b8d2519f1199bfe8e2f78a5f1fd63c2` | [contacts, corners and cover](evidence/8758-cell-contacts.md) |

These twelve contributions contain 105 distinct verified declarations.
The current-policy collection has 266 rows; the old planned root row remains
planned. The latest seven rows have passing canonical build and imported
standard Lean kernel evidence. All 259 parent rows and every original evidence
artifact are preserved unchanged. Do not repeat successful canonical checks
merely because work resumes.

At the latest frozen source, the Geometry target passed in 35.780 seconds and
the imported seven-name audit in 7.741 seconds, without warnings. Only the
three new proof modules and their Geometry aggregator compiled; pinned
Mathlib artifacts were reused. Complete source synchronization passes with
20,220 distinct public references and 20,214 flattened declaration records.
The new chapters have seven mathematical environments, seven declaration
records and six checked proof tags. Generated imports cover 2,848 production
modules in 75 files. Independent mathematical readers approved all seven
statements and proofs.

Source/provenance/generated-import checks for #8870 pass. Full CI and
rendering are separate from the completed local targeted verification;
refresh their statuses before acting. The exact frozen source remains the
source binding for all seven new verification records after metadata changes.

## Current mathematical scope and next action

Distinct actual fine cells are disjoint as half-open sets. For C≥2 and a
reference index k≥50,000,000, a closed intersection of two distinct indexed
fine cells containing two distinct points is a whole side of the smaller
cell. Its opposing side is a whole side or midpoint half, with reversed
orientation and size ratio one or two. The opposing index needs no late bound.
The halves here are from the optional all-midpoint fan.

A contributing coarse dummy-cell corner on a whole or optional elementary
fine side is an endpoint, for C≥2 and k≥k₀, with no late or nonempty-set
premise. For nonempty Z and C≥2, every point outside Nₖ₀ has a unique actual
half-open fine-cell pair (k,z) with k≥k₀. These fine cells and the initial
neighborhood cover the plane exactly.

Two source authors now have disjoint active claims:

- [Actual elementary matching](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6047145012),
  in new `ActualSideMatching.lean`: every actual elementary segment having
  positive-length contact with a distinct actual fine cell must have a segment
  with reversed endpoints under that cell's actual mask. Equal-size sides must
  match even when both are split. For ratio two, the larger mask is true and
  the smaller mask false. No supplied match is assumed.
- [Actual opponent existence](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6047335975),
  in new `ElementarySideOpponents.lean`: the whole closed elementary segment
  must lie in the closed initial neighborhood or a distinct actual fine-cell
  square at an index at least k₀. Derive endpoint-set nonemptiness from actual
  reference membership. Use an outward midpoint neighborhood, a finite local
  cover and corner exclusion; do not assume a contact or covering certificate.

Both files remain outside the current seven-name freeze and imported audit.
Their authors coordinate direct Lean checks so the group runs at most one
such process at a time. Once released, review exact hypotheses against the
source before freezing and verifying each contribution.

For a nonbelt opponent, the existing unique primary theorem supplies its
primary identifier. For a belt opponent, actual elementary matching supplies
the reversed side. Opponent uniqueness, consistent global labels, active rays
and sectors, recursive repairs, descendant estimates, the complete isolated
star lemma and two-family partition remain open. Initial-mark results establish
point separation only. Neither headline theorem is established yet.

## Worktrees and verification discipline

- `worktrees/area-law-peps-models` owns `feat/area-law-cell-contacts` and the
  group's warmed cache. The canonical driver is finished and the shared lock
  released. Preserve the Lean, Mathlib and QICLean pins and existing artifacts.
- `worktrees/area-law-source-preparation` has no `.lake`. It holds two active
  untracked source modules for matching and opponent existence. Preserve both
  when adopting completed evidence or creating the next source branch. Their
  unfinished imports must remain outside a frozen completed contribution.
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

Compression owns #8864, #8866, #8868, #8869 and #8872. The latest owner
handoff reports #8872 at `c54eb4d685ada6d4f69e2e3dcf81960ec1998027`, with
mathematical source `8689eafdd`, for actual selective preparation and common
finite source-gate data derived from the original words. Chronological partial
gate expansion preserving wholly exterior contractions remains active under
#8769. QICLean #571 remains open with its integration contact requested. No
geometry proof assumes that pending integration or proves the full circuit
error theorem.

The analytic group has published QICLean #618 generic Schur mass, #621
uniform-pair occurrence and matching, #622 physical replica gap and sectors,
#624 independent-copy concentration, and #625/#626 good-copy factorization
and permutation covariance. These are owner-reported independently verified
contributions. Actual iid/Schur entropy-compatible sector selection remains
claimed under #8753, with the finite criterion completed and the eventual
specialization being verified. The complete common sequence, physical
Hamiltonian tail estimate and area-law conclusion remain separate obligations.
The geometry group confirms no overlap; no competing analytic model or
dependency adoption is introduced.

Shared storage briefly filled before the source freeze. The sources were
preserved, and another owner removed only their disposable published checkout
and temporary blueprint copies. The geometry group removed no cache or peer
file. Canonical verification resumed with the same warmed artifacts; avoid
creating duplicate caches or worktrees merely to resume.

Check coordination approximately every thirty minutes and before each new
claim or shared-interface change. Direct cross-thread replies are unavailable
in this session; public issue coordination is authorized. Use a small team
with disjoint proof ownership. Continue the active goal without routine
permission requests and report unfinished mathematics accurately.
