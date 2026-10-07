# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
The goal remains active. Both source-faithful headline theorems remain unproved.
The combined fan-contact and primary-cover contribution has completed
source-bound canonical verification and provenance validation. Full CI and PDF/web results are recorded separately
when available; local source synchronization does not replace book compilation.

## Geometric contributions and exact sources

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
| Unique actual opposing region and common elementary-side geometry | [#8892](https://github.com/LionSR/TNLean/pull/8892), evidence `26786e53a29e1804aae6302916b3068ef6cf12e4` | `9e31e29bd1879dac3ae946c0e89e5cdbe9bcc30a` | [unique opponents](evidence/8758-unique-side-opponents.md) |
| Selected opponents, contact characterization and reciprocity | [#8894](https://github.com/LionSR/TNLean/pull/8894), evidence `957de7bed210e037a8a082eae6ad5f9969565fb2` | `b8c1e59e88eadf8694530d1a6fc470d8348c237e` | [reciprocal opponents](evidence/8758-reciprocal-opponents.md) |
| Actual belt-fan colors and retained opposing primaries | [#8895](https://github.com/LionSR/TNLean/pull/8895), evidence `4aaa0256f74aa317cb0180856a9e2579c21b341e` | `acff16af5c9f4726de4efbee7eb01f56729e42b1` | [belt-fan colors](evidence/8758-belt-fan-colors.md) |
| Within-fan contacts and finite fine-cell cover of primaries | Verified successor to [#8895](https://github.com/LionSR/TNLean/pull/8895), on `feat/area-law-fan-primary-contacts` | `26dbf77709501643284144f4294c4d768966958b` | [combined fan/primary evidence](evidence/8758-fan-primary-contacts.md) |

These seventeen contributions contain 121 distinct verified original geometric
declarations. The unchanged current provenance policy passes all 282 records;
the original planned root record remains planned. The combined contribution
adds three verified original records without reverifying any parent declaration.
All 279 parent records and shard bytes, and all 124 tracked historical evidence
files, remain unchanged.

At exact frozen source `26dbf77709501643284144f4294c4d768966958b`, the canonical
Geometry build passed in 17.560 seconds and the imported three-name report in
4.441 seconds without diagnostics. Each report uses only `propext`,
`Classical.choice` and `Quot.sound`. Strict promotion and the unchanged normal
policy pass all 282 records. The evidence finalizer passes; all seven frozen
source, audit and chapter files retain their exact bytes. The final promoted
rows match the raw strict output apart from the three new rows' accurate
historical preparation descriptions. No old proof or record is reverified.

Both full direct package-option checks and complete independent mathematical
reviews pass: FanRunContacts in 17.06 seconds wall, 5.24 seconds user and
6.58 seconds system time; PrimaryFineCellCover in 12.32 seconds wall,
2.35 seconds user and 5.57 seconds system time. Source and chapter reviews
approve all three exact statements and proofs, including the final syntax
corrections and empty, signed and disconnected cases.

Blueprint synchronization passes with `total_blueprint_refs = 20230`; the
flat `blueprint/lean_decls` file contains 20,236 lines. Reverse coverage is
complete. Generated imports cover 2,856 production modules in 75 aggregate
files. The two new chapters contain three theorems, three proofs and three
declaration tags with six completion markers; all dependency labels resolve.
Formatting of both chapters and their parent is idempotent. Reader/module
guards and scoped patterns pass. No repeated three-line proof block was found
in the two new modules; the short endpoint pattern is recorded for later reuse.
The tracked-production guard measures 2,930 files and the all-module guard
3,049. The primary chapter uses floor notation for signed integer division.
Successful canonical checks need no repetition merely because work resumes.

The reciprocal contribution is published as [#8894](https://github.com/LionSR/TNLean/pull/8894)
at evidence head `957de7bed210e037a8a082eae6ad5f9969565fb2`, with source
`b8c1e59e88eadf8694530d1a6fc470d8348c237e`. Its issue handoffs are
[#8758, comment 6048739648](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6048739648)
and tracker comment `6048739882`.
The color contribution is published as draft [#8895](https://github.com/LionSR/TNLean/pull/8895),
at evidence head `4aaa0256f74aa317cb0180856a9e2579c21b341e`, with the exact
verified proof source above. The verified combined successor is recorded by its branch, source and evidence
link, without inventing a new PR number or evidence commit.

Earlier CI observations remain historical: all required #8870 checks passed;
#8876 full Lean, provenance, imports, module and diagram checks passed while
its corrected book retry and compilation-time check were still running or
queued; #8888 full Lean and book checks passed while compilation-time checks
were queued; #8892 checks were then queued. The #8876 interval correction is
preserved at `3da5bcf7053423f16162ad98e126379082d63dff`. These observations
are not a fresh report of those PRs. The pre-existing local whole-library
declaration check failed at missing `TNLean/MPS/Examples/Fibonacci.olean`;
its historical log and limitation remain preserved.

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
every actual elementary segment has a unique dummy-or-fine identifier.
The dummy identifier means containment of the whole segment in the closed
initial neighborhood. A fine identifier specifies an actual distinct cell
at h ≥ k₀ containing the whole segment in its closure. The initial
neighborhood is one region even when several coarse cells contribute.
No contact, cover, opposing label, nonempty-set or sparsity premise is supplied.
The generic elementary-side geometry theorem gives distinct endpoints and
the square's boundary coordinate for arbitrary optional midpoint masks.

The new noncomputable choice selects this unique identifier. For an actual
candidate cell at h ≥ k₀, the choice equals that candidate precisely when
the candidate is distinct from the reference and its closed intersection
with the elementary segment contains two distinct points. This contact
characterization uses the same reference hypotheses and no opposing late
bound. Reciprocity assumes k₀ ≥ 50,000,000, so both reference choices are
available. Selection of the actual candidate is equivalent to distinctness
and the existence of an actual opposing slot with opposite facing side,
reversed endpoints and the reference cell as its selected opponent.
Matching and the return selection are conclusions.

## Actual fan colors and the next claimed obligations

The [four-result color contribution](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6048615708)
is verified on `feat/area-law-belt-fan-colors` at the exact source above.
It defines an actual two-color function on every actual-mask fan slot of a
belt cell for arbitrary origin, endpoint set and dependent residue choices,
C ≥ 2, k₀ ≥ 50,000,000 and an actual belt reference at k ≥ k₀. No sparse-shift
or finite-support assumption is imposed on those choices.

Whole-segment containment in the dummy closure determines the opposite parity
of k₀−1 and proves inequality with the dummy label. Positive contact with an
actual nonbelt cell at h ≥ k₀ retains the explicit shifted pitch index J,
contains the whole elementary segment in that primary birth region, and gives
the opposite primary parity. The primary identifier retains both h and J,
including disconnected fragments. For distinct actual belt cells, any two
actual-mask fan sides whose intersection contains two distinct points have
different colors. Reversed endpoints, a matching slot and a selected-opponent
certificate are not hypotheses. The nested lexicographic order of the layer
and signed cell indices fixes the opposite pair consistently.

The two following modules are now the verified combined successor to the
color contribution:

- [Within-fan triangle and run contacts](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6048750510)
  are assigned to adjacent_scales in `FanRunContacts.lean`. The two generic
  results allow arbitrary origin, scale, signed index and optional midpoint
  mask. They derive consecutive endpoint adjacency and the exact shared radial
  edge from nontrivial triangle contact, then derive different colors for
  distinct actual run components with nontrivial contact. Final full
  package-option elaboration passed without diagnostics in 17.06 seconds wall,
  5.24 seconds user and 6.58 seconds system time. Released SHA-256:
  `4a890d08930fe05e2b7f319d0fc9725937211a4d4db1385db7d8ef1845dd41ed`.
  Independent mathematical review includes the final syntax corrections.
- [Finite fine-cell decomposition of a primary](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6048881242)
  is assigned to polynomial_provenance_review in `PrimaryFineCellCover.lean`.
  Its sole theorem equates an actual primary birth region with the finite
  union of the closed nonbelt fine cells having its shifted pitch index.
  The fine exponent is at most the layer and pitch exponents; no nonempty,
  late-scale, positive-width, retained-index or strict-pitch premise is needed.
  Final full package-option elaboration passed without diagnostics in 12.32
  seconds wall, 2.35 seconds user and 5.57 seconds system time. Released
  SHA-256: `a522974ecffdf40925494a5858fb1a462d5d687a6057349d013e20b93643545b`.
  Independent mathematical review approves the exact statement and proof,
  including signed quotients and empty or disconnected regions.

The two modules now form one combined seventeenth contribution, under their
unchanged public claims. Its completed parent is draft #8895 at evidence head
`4aaa0256f74aa317cb0180856a9e2579c21b341e`. The new immutable baseline measures
279 parent records and 124 tracked historical evidence files. The combined
master adds only three verified original rows, for 282 in total; all parent
records, shards and historical files remain immutable, with no old declaration
reverified. Earlier standalone preparation artifacts remain unchanged.

The combined source is frozen and verified at
`26dbf77709501643284144f4294c4d768966958b` on
`feat/area-law-fan-primary-contacts`. Its canonical build, imported report,
strict promotion, normal policy and metadata finalizer have passed. Root
owns publication of the corresponding evidence; this record assigns no
new PR number or evidence head. All 279 parents and 124 histories and all
seven frozen files remain preserved.

The next generic fan-side boundary reduction is now
[publicly claimed](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6049135316)
in `FanSideContacts.lean`. Its two released statements strengthen the earlier
read-only proposal. A fan triangle meets any whole side of its own square
exactly where its elementary base meets that side. Its intersection with the
closure of any distinct actual fine cell is likewise the base's intersection
with that closure. The proof uses an interior center, convexity and actual
half-open cell disjointness; it needs no lateness, positive-contact or width
bound. Both equalities include empty and singleton contacts and arbitrary
optional midpoint masks.

Released SHA-256:
`1a818c1ab1d6528e11ff7fd784c4357b4d275d4cb0bd29284f0c1be0256fc402`.
The final full package-option check passed without diagnostics in 4.68 seconds
wall, 2.37 seconds user and 2.79 seconds system time. Independent mathematical
review approves the exact released hash and both stronger signatures. The
new module remains outside the combined freeze. Its canonical verification
is pending, and the next two-row provenance preparation leaves its completed
parent BASE and frozen SOURCE unset until the combined evidence head is
provided. No new immutable capture is inferred from expected record counts.

For later interfaces between different cells or disconnected primary unions,
two distinct shared points alone do not certify a positive-length interface.
An actual nondegenerate segment witness is needed for finite extraction of
contacting pieces. The within-one-fan run statement is stronger because every
constituent triangle contains the same center. This distinction remains part
of the proposed global interface argument. Dummy boundary reduction, global
primary/run identifiers and the local sector description are still separate.

Global primary and run labels, active interfaces, local sectors, isolated stars,
recursive repairs and descendant estimates remain further obligations. The
full two-family proposition and both headline theorems remain open. The goal
remains active. QICLean remains pinned to
`8d5389d23c8e675a0117442e1a0d2c683a4bad41`; geometry adopts neither main
integration nor a new dependency pin.

## Worktrees and verification discipline

- `worktrees/area-law-peps-models` is the sole warm worktree, on
  `feat/area-law-fan-primary-contacts` at frozen source
  `26dbf77709501643284144f4294c4d768966958b`. Its canonical build and
  imported report have passed. Preserve all seven frozen files and cached
  dependencies during metadata publication; no second verification is needed.
- `worktrees/area-law-source-preparation` has no `.lake`; its successor branch
  is `feat/area-law-fan-run-contacts`, observed at completed color evidence
  `4aaa0256f74aa317cb0180856a9e2579c21b341e`. Both released successor files
  remain preserved. All future advances and production changes belong to root.
- Canonical builds and cache mutations use the warm worktree's own locked
  wrapper. The shared lock waits without consuming CPU. Direct source checks
  use the warm environment and package options, with one process at a time.
  Do not rebuild Mathlib, clear artifacts or create a second warm cache.
- Hot-main and dependency integration remain with their coordinating owners.
  Do not reset peer worktrees, interrupt builds, merge main or change pins.

## Other owners and coordination

The earlier coordination record observed main at
`80bc49d17e833795fba00bfeaf1bd053649c4070`, all required #8826 checks passing,
and #8798 book checks passing with its Lean build still pending. It also
recorded passing boundary #8849 checks and passing scanner #8834 Lean/policy
checks, with rendering separately tracked. These are preserved historical
observations rather than a new CI query. Their model and dependency integration
remain separate from this group's fixed QICLean pin.

Capped-partition #8863 remains at `b6f1f462`. Earlier compatible warm review
passed its production target. Strict regression and imported-report commands
encountered documentation or resource-limit diagnostics; all 23 printed
reports satisfy the standard logical-foundation policy. The exact findings
remain in the [review](https://github.com/LionSR/TNLean/pull/8863#issuecomment-6046537485)
and [handoff](https://github.com/LionSR/TNLean/issues/8754#issuecomment-6046800493).
Its owner retains the corrective work; no repeated production check is needed.

Compression retains #8864, #8866, #8868, #8869, #8872 and
[#8887](https://github.com/LionSR/TNLean/pull/8887), published at
`cc0a19f9b2f35b5bd843bd82e9b0e2cecbdcdccb`. The owner reports checked
chronological expansion and fixed-source operator identities. Its next
19-declaration source is `6246647741ce41a55a3897329336055330dd7e6f`;
it is published as [#8893](https://github.com/LionSR/TNLean/pull/8893),
with exact head `4097a00b1ea14529fad15cb6d22d1b82c273e2db`.
Its owner reports the completed source checks; full PR checks remain separate.
Compression owns the TNLean integration of this fixed source. The physical
output and discarded-register protocol producer remains unidentified in the
shared coordination record. The geometry group's
[latest reply](https://github.com/LionSR/TNLean/issues/8769#issuecomment-6048944864)
confirms that geometry has no verified producer and introduces no competing
model.
These owner reports do not establish the compression headline theorem.

The analytic group's actual prevector contribution is published as
[QICLean #631](https://github.com/LionSR/QICLean/pull/631) at exact head
`859f992782a0b78c48a397b957012749936c4837`. Its owner reports complete
source-bound verification of one sequence with the required properties at
every positive index after a finite initial repair. Earlier marginal,
projection and entropy-sequence contributions remain with that group.
The analytic owner has the separate QICLean source integration against main
`48425ea8` and the assigned #571 source, preserving theorem statements and
proofs. Neither that integration nor compression's TNLean integration is
adopted by geometry. The newer scalar-count contribution is published as
[QICLean #636](https://github.com/LionSR/QICLean/pull/636), at confirmed PR head
`3b78880a454ac12f31df3f2fe7079a1544956487`. Its owner reports verified source
`40d9ab9e`, four scalar-count results, 9,761 full records and 3,381 native
records. Root confirmed the PR head; these source and count reports remain
attributed to their owner rather than independently reverified by geometry.
They do not establish an inversion bound. No completed comparator,
inverse-metric comparison, physical tail bound or area-law theorem is claimed.

The [latest ownership reply](https://github.com/LionSR/TNLean/issues/8769#issuecomment-6048944864)
records the separate analytic QICLean and compression TNLean integration
responsibilities. Check coordination approximately every thirty minutes and
before each new claim or shared-interface change. Public issue coordination
is authorized. Use a small team with disjoint ownership and continue the
active goal while reporting unfinished mathematics accurately.
