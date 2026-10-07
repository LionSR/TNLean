# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
Last coordination refresh: October 7, 2026, 22:40–22:46 UTC.
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
| Fine-cell contacts, dummy corners and exact fine-cell assignment | [#8876](https://github.com/LionSR/TNLean/pull/8876) | `0ac139a04b8d2519f1199bfe8e2f78a5f1fd63c2` | [contacts, corners and cover](evidence/8758-cell-contacts.md) |
| Common side endpoints, actual elementary matching and opponent existence | [#8888](https://github.com/LionSR/TNLean/pull/8888), evidence `eda992e719dd7161906b54b20a057992037b44cb` | `93c807b97f45312bab807ba47abb06f11d686f18` | [matching and opponents](evidence/8758-actual-side-matching.md) |
| Unique actual opposing region and common elementary-side geometry | `feat/area-law-unique-side-opponents`, based on #8888 | `9e31e29bd1879dac3ae946c0e89e5cdbe9bcc30a` | [unique opponents](evidence/8758-unique-side-opponents.md) |

These fourteen contributions contain 111 distinct verified declarations.
The current-policy collection has 272 rows; the original planned root row
remains planned. The latest two public theorems and the unchanged old existence
statement have exact-source canonical build and standard Lean kernel evidence.
All other 269 parent records and all 112 tracked historical evidence files
remain unchanged. The existence record receives fresh verification because its
complete source file now exports the unchanged elementary-boundary helper.
Its original evidence at 93c807b97f45312bab807ba47abb06f11d686f18 is retained.

At frozen source 9e31e29bd1879dac3ae946c0e89e5cdbe9bcc30a, the Geometry
build passed in 27.361 seconds and the three-name imported report in 20.998
seconds, without warnings. Only the changed old opponent module, new uniqueness
module and their aggregator compiled. Prebuilt Mathlib and existing TNLean
artifacts were reused. Complete source synchronization passes with 20,226
distinct references and 20,220 flattened declaration records. The new chapter
contains two mathematical statements, two declaration records and two proofs.
Generated imports cover 2,852 production modules in 75 files. Independent
review approves both new results and the unchanged old existence signature.
Do not repeat successful canonical checks merely because work resumes.

Full Lean CI and every required check for #8870 pass. For #8876, full Lean,
provenance, imports, module and compile-time checks pass at 863405980. Its
blueprint lint failed on repeated half-open interval brackets, before PDF/web
compilation. A one-line notation correction at 3da5bcf7053423f16162ad98e126379082d63dff
uses the standard left-bracket macro. The exact CI PCRE warning pattern
matches the original and excludes the corrected file and the three new chapters.
Local ChkTeX uses a different regex implementation; remote book retry remains
pending. Local source
synchronization does not replace PDF/web compilation. The older local
whole-library declaration check failed at a missing pre-existing
Fibonacci.olean; its historical log remains preserved.

## Current mathematical scope

Distinct actual fine cells are disjoint as half-open sets. For C ≥ 2 and a
reference index k ≥ 50,000,000, a closed intersection of distinct indexed fine
cells containing two distinct points is a whole side of the smaller cell.
The opposing side is a whole side or midpoint half, with opposite facing side
indices and size ratio one or two. The opposing layer needs no late bound.

Contributing coarse dummy corners on a whole or optional elementary fine side
are endpoints, for C ≥ 2 and k ≥ k₀, without a late or nonempty-set premise.
For nonempty Z and C ≥ 2, each point outside Nₖ₀ has a unique actual half-open
fine-cell pair (k,z), with k ≥ k₀. Together these cells and Nₖ₀ cover the plane.

Under C ≥ 2, reference k ≥ 50,000,000, k₀ ≤ k,h, both actual memberships and
distinct indexed cells, every actual elementary segment whose intersection
with the opposing closed cell contains two distinct points matches a segment
under that cell's actual mask. Their endpoints are reversed and their facing
side indices differ by two. Equal-sized divided sides match half by half;
for size ratio two, the larger side is divided and the smaller is undivided.

Under C ≥ 2, reference k ≥ 50,000,000, k₀ ≤ k and actual reference membership,
every actual elementary segment lies in the closed initial neighborhood or
one distinct actual closed fine cell at an index h ≥ k₀. The finite outward
cover supplies the opponent; corner exclusion extends contact across the
whole segment. Endpoint-set nonemptiness is derived. No contact, cover,
opposing label or sparsity certificate is supplied.

## Unique opposing regions and next action

The [opponent-uniqueness claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6047895365)
and [shared-geometry extension](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6047933668)
are implemented and independently approved. At frozen source
`9e31e29bd1879dac3ae946c0e89e5cdbe9bcc30a`, the canonical Geometry build
passed in 27.361 seconds and the three-name imported report in 20.998
seconds, both without diagnostics. The three reports use only the standard
logical foundations. The strict helper produced two new verified records
and fresh verification for the unchanged opponent-existence statement.
The unchanged normal current-policy check also passes all 272 records.
The contribution is prepared for draft publication; its public handoff
records the publication and exact evidence head.

With exactly the existence hypotheses—C ≥ 2, reference k ≥ 50,000,000,
k₀ ≤ k and actual reference membership—every actual elementary segment
has a unique identifier in Option (ℕ × (ℤ × ℤ)). The dummy identifier
means containment of the whole segment in the closed initial neighborhood.
An actual fine-cell identifier has h ≥ k₀, actual membership, distinctness
from the reference pair and whole-segment closed-cell containment. The dummy
neighborhood is one region, even when several coarse cells contribute.
Uniqueness follows from actual disjointness and the impossibility of three
rectangles with disjoint interiors sharing an interior side midpoint, with
corner exclusion preventing a tangential endpoint there.

The common elementary-side geometry theorem is the parent private statement
and proof exported unchanged as cellFan_elementary_geometry; its two callers
use the new name without an alias. For arbitrary optional midpoint masks,
every elementary side has distinct endpoints and a constant coordinate equal
to a boundary coordinate of its square. It needs no layer or late hypothesis.
The old existence statement and all its other proof steps are unchanged.

The completed parent is #8888 at `eda992e719dd7161906b54b20a057992037b44cb`.
The verified full collection contains 272 entries: two new records and
one reverified old record, with the other 269 parent records unchanged. The
stronger immutable baseline preserves every one of the 112 tracked historical
files recursively under docs/provenance/evidence, including all notes and
imported reports. Original existence evidence at source
`93c807b97f45312bab807ba47abb06f11d686f18` is retained. Full source
synchronization and changed-declaration reverse coverage pass with 20,226
distinct references and 20,220 declaration records. Generated imports cover
2,852 production modules in 75 files. The new scoped chapter has two
statements, two declaration records and two proofs; formatting is idempotent.
Source guards and reader-facing prose pass. Full CI and book compilation
remain pending. The historical missing-Fibonacci local limitation remains
recorded.

The [claimed successor](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6048409373)
is a new ElementarySideReciprocity.lean module with elementarySideOpponent,
elementarySideOpponent_eq_some_iff_contact and elementarySideOpponent_reciprocal_iff.
The choice and contact characterization use exactly the existing reference
hypotheses; the candidate contact theorem adds actual candidate membership
and h ≥ k₀, without an opposing late bound. Reciprocity uses k₀ ≥ 50,000,000
to make both reference choices available and derives an actual opposing slot
with reversed endpoints and the reference cell as its selected opponent.
Matching and the return identifier are conclusions. The reverse direction
uses endpoint contact without circular dependence on reciprocity.

One author owns only this successor module and the group's sole direct Lean
check slot. Root owns the completed uniqueness sources, imports, notices,
blueprint and evidence. The successor remains outside the current source
freeze, aggregate import and three-name report. Once released, review its
exact statement and proof, then freeze and verify one combined contribution.
No old subdivision-mask promotion or slot-uniqueness machinery is required.

Actual-cell uniqueness does not yet assign a primary identifier to each
opponent. For a nonbelt opponent, the existing unique-primary theorem supplies
that identifier. Compose these data with actual fan runs and consistent global
labels, then construct the active interfaces and local sectors. Reuse the
existing affine-mesh supporting-line clearance. Recursive repairs, descendant
estimates, isolated stars, the full two-family proposition and both headline
theorems remain open. QICLean remains pinned to
`8d5389d23c8e675a0117442e1a0d2c683a4bad41`; dependency integration stays with
its coordinating owner. The latest compression clarification separates
[future integration ownership](https://github.com/LionSR/TNLean/issues/8769#issuecomment-6048356774)
from the physical/discarded-register producer, whose owner is still unidentified.

## Worktrees and verification discipline

- worktrees/area-law-peps-models owns feat/area-law-unique-side-opponents and
  the group's only warm cache. Its canonical build and imported reports are
  finished at 9e31e29bd, and the shared lock is released. Metadata changes preserve every frozen production,
  audit and new blueprint byte. Preserve all toolchain and dependency pins.
- worktrees/area-law-source-preparation has no .lake and was detached clean
  at frozen source 9e31e29bd when the successor branch was created. It now owns
  feat/area-law-reciprocal-side-opponents and the separate new reciprocal
  module. Fast-forward completed evidence while preserving that untracked
  successor. Keep it outside current imports and verification until release.
- Canonical builds and cache mutations use the worktree's own locked wrapper.
  The shared kernel lock waits without consuming CPU. Direct source checks
  use the warm environment and package options, one process at a time.
  Do not rebuild Mathlib, clear artifacts or create a second warm cache.
- Hot-main and dependency integration remain with their coordinating owner.
  Do not reset peer worktrees, interrupt builds, merge main or change pins.

## Other owners and coordination

Main was observed at 80bc49d17e833795fba00bfeaf1bd053649c4070. Template
integration #8798 (077f62c33) and boundary integration #8826 (2ed6f6ed) retain
model cd7271b9 and QICLean 83fdc804. All required #8826 checks now pass;
#8798 has passing book checks and an active Lean build.
This group retains QICLean 8d5389d2 until coordinated adoption. Boundary
#8849 has passing checks; scanner #8834 has passing Lean/policy checks with
rendering separately tracked. Their entropy conclusions remain separate.

Capped-partition #8863 remains at b6f1f462. Compatible warm review passed the
production target in 9.080 seconds. Strict regression failed in 11.971 seconds
at missing documentation and concrete resource limits; the strict audit exited
1 in 7.658 seconds at documentation/hash-command linters. All 23 printed reports
satisfy the unchanged standard logical-foundation policy. The precise logs and
repairs are in [the review](https://github.com/LionSR/TNLean/pull/8863#issuecomment-6046537485)
and [handoff](https://github.com/LionSR/TNLean/issues/8754#issuecomment-6046800493).
The owner must correct and recheck those diagnostic files. No repeat of the
unchanged production proof or peer source/cache/ledger mutation is required.

Compression retains #8864, #8866, #8868, #8869, #8872 and
[#8887](https://github.com/LionSR/TNLean/pull/8887), whose published head is
cc0a19f9b2f35b5bd843bd82e9b0e2cecbdcdccb. The owner reports checked actual
chronological expansion, common fixed source slots, original source occurrences
and exact operator identities. The fixed-slot producer and actual separated
source contractions remain active. Geometry has no competing integration
branch. The compression owner may coordinate additive integration with the
hot-main owner after its next fixed-source freeze. The concrete physical-output
and discarded-register protocol producer, and its local tensor-network T,
remain [queried](https://github.com/LionSR/TNLean/issues/8769#issuecomment-6048356774).
These developments do not establish the full compression theorem.

The analytic group retains QICLean #618, #621, #622, #624–627 and the newly
published [#628](https://github.com/LionSR/QICLean/pull/628),
[#629](https://github.com/LionSR/QICLean/pull/629) and
[#630](https://github.com/LionSR/QICLean/pull/630). Their reported exact heads
are d94e6c04ad860ace732ad0099828bbc62e5f391c,
8042dcf9c8d8c659599fd1130740ca9d21088a9a and
18155980ade0fce287c18e84a5b6ba3d5a8de185, respectively. Actual marginal and
projection identities, the common entropy-compatible high-label sequence and
grouped-label inequalities have reported complete source-bound build, kernel
and PDF/web checks. The sequence has eventual inverse-polynomial mass and
log dimension k S(ρ) + o(k), including singular densities.

The actual prevector source f0c7d137371f6b11ca1dd61692be37581c8adbaf has
passed reported strict checking and independent review, with full source-bound
verification underway. Its single sequence now has the required properties
at every positive index after a finite initial repair. Bad-copy dimensions,
Bell-data instantiation and exact-excitation component symmetry remain with
that owner. No completed comparator, inverse-metric comparison, physical tail
bound or area-law theorem is claimed. Geometry has no overlapping analytic
implementation and preserves its dependency pin. The latest
[coordination refresh](https://github.com/LionSR/TNLean/issues/8753#issuecomment-6048383780)
records these separate responsibilities.

Check coordination approximately every thirty minutes and before each new
claim or shared-interface change. Direct cross-thread replies are unavailable;
public issue coordination is authorized. Use a small team with disjoint
ownership. Continue the active goal without routine permission requests and
report unfinished mathematics accurately.
