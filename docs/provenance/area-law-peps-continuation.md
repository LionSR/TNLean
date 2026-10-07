# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
The goal remains active. Both source-faithful headline theorems remain unproved.
The current belt-fan color contribution has completed source-bound local and
canonical verification. Full CI and PDF/web results are recorded separately
when available; local source synchronization does not replace book compilation.

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
| Unique actual opposing region and common elementary-side geometry | [#8892](https://github.com/LionSR/TNLean/pull/8892), evidence `26786e53a29e1804aae6302916b3068ef6cf12e4` | `9e31e29bd1879dac3ae946c0e89e5cdbe9bcc30a` | [unique opponents](evidence/8758-unique-side-opponents.md) |
| Selected opponents, contact characterization and reciprocity | [#8894](https://github.com/LionSR/TNLean/pull/8894), evidence `957de7bed210e037a8a082eae6ad5f9969565fb2` | `b8c1e59e88eadf8694530d1a6fc470d8348c237e` | [reciprocal opponents](evidence/8758-reciprocal-opponents.md) |
| Actual belt-fan colors and retained opposing primaries | `feat/area-law-belt-fan-colors`, verified contribution | `acff16af5c9f4726de4efbee7eb01f56729e42b1` | [belt-fan colors](evidence/8758-belt-fan-colors.md) |

These sixteen contributions contain 118 distinct verified geometric declarations.
The unchanged current-policy validator passes all 279 records; the original
planned root record remains planned. The color contribution adds four verified
records without reverifying any parent declaration. All 275 parent records and
shard bytes, and all 120 tracked historical evidence files, remain unchanged.

At exact frozen source `acff16af5c9f4726de4efbee7eb01f56729e42b1`, the
canonical Geometry build passed in 15.499 seconds and the imported four-name
kernel report in 4.525 seconds, without diagnostics. Every report uses only
`propext`, `Classical.choice` and `Quot.sound`. The final direct source check
with package options passed without diagnostics in 14.91 seconds wall time,
2.49 seconds user time and 7.22 seconds system time. Strict promotion and the
post-copy normal policy check both pass all 279 records. The five frozen
source, audit and blueprint files remain byte-identical. Root's dependency
review and the independent complete mathematical review approve the source.

Complete source synchronization and changed-declaration reverse coverage pass
with 20,233 distinct references and 20,227 flattened declaration records,
without missing, stale or duplicate references. Generated imports cover 2,854
production modules in 75 files. The new chapter contains one definition,
three theorems and three proofs, with seven completed declaration/proof tags.
Pinned formatter idempotence, module guards, reader-facing prose and scoped
pattern checks pass. No repeated current three-line proof pattern was found.
Successful canonical checks need no repetition merely because work resumes.

The reciprocal contribution is published as [#8894](https://github.com/LionSR/TNLean/pull/8894)
at evidence head `957de7bed210e037a8a082eae6ad5f9969565fb2`, with source
`b8c1e59e88eadf8694530d1a6fc470d8348c237e`. Its issue handoffs are
[#8758, comment 6048739648](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6048739648)
and tracker comment `6048739882`.

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

Two disjoint successors are complete at the direct-source level and remain
outside the current color source freeze and imported report:

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

No canonical verification of either successor is recorded yet. Preserve their
released, untracked files while adopting the completed color evidence. Root
owns subsequent notice installation, imports, blueprint, source freeze and a
single combined canonical verification. Adjacent_scales is independently
scouting boundary and base contacts read-only. The prospective FanRunContacts
provenance artifacts remain below /tmp with their parent baseline unset until
the completed color publication is supplied and its actual inventory measured.

Global primary and run labels, active interfaces, local sectors, isolated stars,
recursive repairs and descendant estimates remain further obligations. The
full two-family proposition and both headline theorems remain open. The goal
remains active. QICLean remains pinned to
`8d5389d23c8e675a0117442e1a0d2c683a4bad41`; geometry adopts neither main
integration nor a new dependency pin.

## Worktrees and verification discipline

- `worktrees/area-law-peps-models` is the sole warm worktree, on
  `feat/area-law-belt-fan-colors` at frozen source
  `acff16af5c9f4726de4efbee7eb01f56729e42b1`. Its canonical build and
  imported report are complete. Preserve all five frozen files and cached
  dependencies during the metadata publication.
- `worktrees/area-law-source-preparation` has no `.lake`; its successor branch
  is `feat/area-law-fan-run-contacts` at completed reciprocal evidence
  `957de7bed210e037a8a082eae6ad5f9969565fb2`. Root will advance it to the
  completed color evidence while preserving both released successor files.
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
adopted by geometry. No completed comparator, inverse-metric comparison,
physical tail bound or area-law theorem is claimed.

The [latest ownership reply](https://github.com/LionSR/TNLean/issues/8769#issuecomment-6048944864)
records the separate analytic QICLean and compression TNLean integration
responsibilities. Check coordination approximately every thirty minutes and
before each new claim or shared-interface change. Public issue coordination
is authorized. Use a small team with disjoint ownership and continue the
active goal while reporting unfinished mathematics accurately.
