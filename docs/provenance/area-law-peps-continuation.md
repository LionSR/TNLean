# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
Last coordination check: October 7, 2026, 19:19 UTC.

## Verified mathematical contributions

| Contribution | Pull request | Exact verified source | Published evidence head |
|---|---|---|---|
| Fine-cell refinement and sparse-belt decay | [#8837](https://github.com/LionSR/TNLean/pull/8837) | `fc87534a119694461e9c3d3c37a7bfa1bf3ea960` | `4e12e35eb90436f776d998345950e70bfdce68b2` |
| Uniform separation of dyadic scales | [#8846](https://github.com/LionSR/TNLean/pull/8846) | `4be0ad6b5e6bc2d1523ba02b8675377c05549da5` | `44615152fb68de9bc913f491231dd7325f3fdef4` |
| Polynomial absorption and the numerical series bound | [#8848](https://github.com/LionSR/TNLean/pull/8848) | `5652d02446787ee2b9248db1057df48adbe32492` | `ed84770bf703478d69e4c8625d005c645d1a2529` |
| Primary birth regions, rectangular fragments and adjacent meshes | [#8851](https://github.com/LionSR/TNLean/pull/8851) | `d469be1a0a7799f4613e64e8139893b0fa2ee11d` | `fd8bf12587482c1db66c8c626a9df57cc4db025f` |
| Number of actual primary identifiers | [#8856](https://github.com/LionSR/TNLean/pull/8856) | `b1dc393c764962cbc0cfb4c1bbefd3519c04a967` | `61fd819e7fe4689b8e0893affc9f127238b191ec` |
| Actual nine-point belt marks and their sparse count | [#8857](https://github.com/LionSR/TNLean/pull/8857) | `0b1556b85180ed55e2a1db6ada9f44cc24a8df2b` | `98d26cdad5e212a7e241951618dd3645f3ae6b21` |
| Quarter-mesh bounds and neighboring-layer locality | [#8859](https://github.com/LionSR/TNLean/pull/8859) | `5db13f626cbba4ce128e25ddcdb60a00532f0f3a` | `436ea587677e61b2e971555cdf612ba1be6006cd` |
| Actual finite initial marks, minimum sides and point separation | Publication accompanies this record | `5d2246bb32045fafea826200dd09b3518629ae97` | Evidence commit containing this record |

All 64 exact imported declarations in these eight contributions have passing
canonical build and standard-axiom evidence. Complete provenance validation
passes 225 entries. The four initial-family/separation rows alone were promoted
in the latest contribution; all previous 221 records and their evidence remain
unchanged. The old planned root-ledger row remains planned.
Commands, logs, hashes and mathematical scope are recorded in
[fine belts](evidence/8758-fine-belts.md),
[scale separation](evidence/8758-scale-separation.md),
[polynomial sums](evidence/8758-polynomial-budget.md),
[primary regions](evidence/8758-primary-regions.md), and
[primary counts](evidence/8758-primary-count.md), and
[belt marks](evidence/8758-belt-marks.md), and
[mesh and locality](evidence/8758-quarter-mesh.md), and
[the initial mark family](evidence/8758-initial-mark-family.md).
These proofs must not be rebuilt merely because work resumes.

The first three drafts have passing full Lean builds, compiled blueprint
checks, rendering and module policies. The polynomial draft's failed timing
job had no diagnostic log; its failed-only rerun passed. The fine-belt draft
had two approvals on its exact published head. All checks on #8851 and #8856 now pass, including compiled declarations and rendering. #8857's full Lean build and diagram checks pass, with rendering and timing pending. #8859 remains in full CI. Refresh external statuses
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
warnings and independent mathematical review. Canonical Geometry compilation
passed in 15.964 seconds and the six-name imported audit in 4.331 seconds, at
the exact source in the table. Only the three standard logical axioms occur.
Their six provenance rows now have completed evidence in the 215-entry collection.
Source: Section 11, lines 325–330 of the pinned manuscript. The proof author
owns only the new Lean file; separate reviewers handle source and provenance.
The root agent owns imports, blueprint, canonical verification and publication.

Contacts, actual fans and merged identifiers, the ray and sector assertions of
isolated stars, descendant estimates, simultaneous repairs, separation from
earlier birth regions and the complete two-family partition remain open.
Mixed-scale mesh point and nonincident-line separation are verified prerequisites;
the actual minimum-scale family and point-separation assertion are now prepared. The straight-ray
conclusion must be proved on actual tile regions. Polynomial summability does
not count actual repairs. Both source-faithful headline theorems remain unproved.

## Worktrees and evidence preservation

- `worktrees/area-law-peps-models` holds `feat/area-law-initial-mark-family`. Its
  canonical four-declaration driver has finished and released the shared lock. The
  existing warmed cache and all package pins remain unchanged.
- `worktrees/area-law-source-preparation` holds `feat/area-law-cell-fans`,
  initially based on the frozen initial-family source `5d2246bb`. It has no
  `.lake` directory. Merge completed parent evidence before freezing the fan
  contribution, then move the branch to the warmed worktree for one targeted check.
- The prior canonical checks and logs must not be repeated. Never clear or
  reseed this warmed cache merely to prepare another auxiliary contribution.
- The hot-main worktree belongs to the coordinating owner. Do not reset an
  active peer worktree, interrupt its build or change dependency pins.

The completed six-declaration mesh and local-layer contribution follows the
[quarter-mesh claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6044056435)
on `feat/area-law-quarter-mesh`. Its new `MeshGeometry.lean` concerns a translated
mesh, separation of distinct points, clearance from a nonincident affine line
of an allowed slope, and membership of the actual belt marks at neighboring
scales. The author owns only this new Lean file; independent reviewers inspect
the source and prepare provenance, while the root agent owns blueprint and
canonical verification. Its four mesh names are `affineMesh`,
`beltMarks_subset_affineMesh`, `affineMesh_dist_ge` and `affineMesh_line_dist_ge`.
The [locality extension](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6044139454)
adds `LocalLayers.lean`, owned by the root agent, with
`dyadicLayer_dist_nonadjacent_fineScale` and `dyadicLayer_nearby_indices`.
For C₀ ≥ 2 and k ≥ 50,000,000, nonadjacent closed layers have distance at
least 16t_k; a distance below 10t_k forces adjacent indices. Both files pass
package-option non-mutating elaboration without warnings and independent
review. Complete static provenance validation passes 221 entries; the six
new rows now have completed canonical evidence at the exact source above.
The combined Geometry build passed in 13.186 seconds and its six-name imported
audit in 4.067 seconds, without warnings and with only standard logical axioms.
Full source synchronization and reverse coverage passed for all 20,175 public
references and 20,169 entries; full CI and rendering remain pending.
Source: Section 11, lines 352–359. This numerical contribution does not claim
the full isolated-star statement or the construction of active interfaces.

The next [initial-mark-family claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6044473740)
is on `feat/area-law-initial-mark-family`. Its
[minimum-scale and separation extension](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6044749108)
adds one disjoint geometric module. `InitialMarkFamily.lean` has three public
theorems: actual sparse residue functions with finite nonempty-cell support;
the exact finite mark union above any lower index with a uniform boundary
count; and that same construction with positive attained minimum incident
sides and pairwise separation. The support may be empty. For C₀ ≥ 2 and
k₀ ≥ 50,000,000 the final inequality is
`dist(v,w) ≥ max(S(v),S(w))/4` for distinct actual marks. The constant B is
chosen before origin, domain, cut, radius and starting index. A least incident
layer gives an actual selected cell witness and comparison with every incident
selected cell in the constructed family.

`FineMarkSeparation.lean`, owned by the root agent, has the single public
`fineLayer_marks_dist_ge`. For any two actual fine-layer cells with C₀ ≥ 2 and
both layer indices at least 50,000,000, distinct cell marks have distance at
least one quarter of the larger cell side. Closure membership includes cell
boundary marks. This applies to all actual fine-layer cells and therefore to
the selected belt cells; no assumed fan interface or isolated-star property
is used. The author and independent reviewer have approved all four signatures
and proofs. Package-option direct elaboration of the combined source passes
without warnings. No new structure or predicate is introduced.
Source: Section 11, lines 220–233, 325–339, 352–363 and 668–692.

The four-name canonical Geometry build passed at `5d2246bb` in 29.380 seconds
(FineMarkSeparation 18 seconds, InitialMarkFamily 3.5 seconds, aggregator 2.8
seconds). The exact imported audit passed in 4.380 seconds with only standard
logical axioms. Only those four new rows were promoted; the complete 225-entry
policy/source/license/notice/evidence validation passes with the 221-entry
parent baseline byte-identical. Full blueprint source synchronization passes
20,179 distinct public references and 20,173 entries, with complete reverse
coverage of the changed declarations, and formatter/import checks pass.
Full CI and rendering remain pending; the known unrelated local declaration
artifact limitation is preserved without another failed whole-library check.

The next [single-cell fan claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6045048500)
is on `feat/area-law-cell-fans`, in new `Geometry/CellFans.lean`, owned by the
proof author. Each side of an actual dyadic square may remain whole or split
at its midpoint. Joining the center to these elementary segments produces
four to eight actual TemplatePolygon triangles. The target is exact closed
cell cover, allowed slopes and shared-boundary geometry. It will not assume
or claim the later opposing-region assignment, cyclic equal-label merging,
active interfaces or the full isolated-star ray/sector assertion. Source:
Section 11, lines 299–310. Independent review and Mathlib scouting are underway.

The next local action is to publish the complete initial-family evidence and
draft, merge that evidence into preparation, and complete the cell-fan proofs.
Preserve the completed 225-entry baseline when preparing the new fan rows.
Canonical builds, cache mutations and parent source checks are not to be repeated.

At the latest coordination check, the boundary comparisons were ready in
[#8849](https://github.com/LionSR/TNLean/pull/8849); the analytic owner published
separate entropy/radius arithmetic in [#8854](https://github.com/LionSR/TNLean/pull/8854)
and quantum-information results in [QICLean #605](https://github.com/LionSR/QICLean/pull/605).
Their compressed selected-vector construction is disjoint from the geometry.
Main has advanced to `e3e3dddb429a61dd710ec9c8a3635ba6460ae222` with
PEPS whole-group truncation #8799 and exact dyadic routing #8796 merged.
Their work remains with its owners. Template owners were testing main
`18a6dd4d` with QICLean `83fdc804`;
this geometric branch preserves its own verified pins until coordinated
integration. The compression owner published unused-pair one-dimensional padding in
[#8860](https://github.com/LionSR/TNLean/pull/8860), source `8eccd116408d22a115220881e7e07c96aa4f23ea`,
evidence head `fb4719ad38e905d5dde1fbb1e8e077d05155939b`, after #8858; analytic tail-to-state consequences are published in QICLean
#608, and the exact one-copy Bell projection remains with the analytic owner.
The same compression group is preparing the actual common branch-slot assignment
using QICLean #571, after checking #8769 ownership. Geometry does not own that
construction. The analytic typical-state group has claimed the narrow scalar tail specialization
in #8753 comment6044688756; it does not establish the native Hamiltonian tail
or lattice budget. The coherent dependency pin remains separate.
No model, entropy, scanner, QICLean or PEPS ownership is changed.

The earlier [geometry handoff](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6042318628)
and [tracker handoff](https://github.com/LionSR/TNLean/issues/8733#issuecomment-6042338516)
record previous contribution boundaries. No main-branch merge or dependency-pin
change was performed by this contribution.
