# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
The goal remains active. Both source-faithful headline theorems remain unproved.
The current reciprocal contribution has completed local verification.
Its full CI and PDF/web checks remain pending.

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
| Selected opponents, contact characterization and reciprocity | `feat/area-law-reciprocal-side-opponents`, locally verified draft contribution | `b8c1e59e88eadf8694530d1a6fc470d8348c237e` | [reciprocal opponents](evidence/8758-reciprocal-opponents.md) |

These fifteen contributions contain 114 distinct verified declarations.
The unchanged current-policy validator passes all 275 records; the original
planned root record remains planned. The reciprocal contribution adds three
verified records, without reverifying any parent declaration. All 272 parent
records and shard bytes, and all 116 tracked historical evidence files, remain
unchanged.

At exact frozen source `b8c1e59e88eadf8694530d1a6fc470d8348c237e`, the
Geometry build passed in 16.406 seconds and the three-name imported kernel
report in 4.288 seconds, without diagnostics. Only the new reciprocity module
and Geometry aggregator compiled; existing artifacts and the prebuilt Mathlib
cache were reused. All three reports use only `propext`, `Classical.choice`
and `Quot.sound`. Strict promotion and the post-copy normal policy check both
pass all 275 records. The six frozen source, audit and blueprint files remain
byte-identical.

Complete source synchronization and changed-declaration reverse coverage pass
with 20,229 distinct references and 20,223 flattened declaration records,
without missing, stale or duplicate references. Generated imports cover 2,853
production modules in 75 files. The new chapter contains one definition,
two theorems, three declaration records and two proofs. Independent review,
pinned formatter idempotence, module guards and reader-facing prose checks
pass. The older matching chapter's closing paragraph now points to opponent
uniqueness; its mathematical statements and proofs are unchanged. Successful
canonical checks need no repetition merely because work resumes.

Full Lean CI and every required check for #8870 pass. For #8876, full Lean,
provenance, imports, module and diagram checks pass; the corrected book
retry is running and the compilation-time check is queued. Its one-line interval-notation correction is preserved at
`3da5bcf7053423f16162ad98e126379082d63dff`. The #8888 full Lean and book checks pass, with its compilation-time check
queued. The #8892 checks remain queued. Source synchronization does not replace PDF/web
compilation. The older local whole-library declaration check failed at the
pre-existing missing `TNLean/MPS/Examples/Fibonacci.olean`; its historical
log and limitation remain preserved.

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

## Claimed color successor and next action

The [four-result color contribution](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6048615708)
is claimed in the source-only branch `feat/area-law-belt-fan-colors`, based
on the reciprocal source above. Its author owns only the new BeltFanColors.lean
module and the group's sole direct source-check slot. These unfinished results
remain outside the completed reciprocal source freeze, imports and report.
Root owns publication of the reciprocal evidence and the eventual aggregate
imports and verification of the successor. Adopt the completed reciprocal
evidence while preserving the author's separate source work.

Consistent primary and dummy labels, active interfaces, local sectors,
isolated stars, recursive repairs and descendant estimates remain further
obligations. The full two-family proposition and both headline theorems remain
open. QICLean remains pinned to
`8d5389d23c8e675a0117442e1a0d2c683a4bad41`; this geometric contribution
neither merges main nor adopts a new dependency pin.

## Worktrees and verification discipline

- `worktrees/area-law-peps-models` owns
  `feat/area-law-reciprocal-side-opponents` and the group's only warm cache.
  Its canonical checks are finished at the frozen source above and the shared
  lock is released. Metadata changes preserve all six frozen files.
- `worktrees/area-law-source-preparation` has no `.lake` and owns the
  color successor branch, based on the same frozen source, with the author's
  separate new module. Keep unfinished work outside current verification.
- Canonical builds and cache mutations use the worktree's own locked wrapper.
  The shared lock waits without consuming CPU. Direct source checks use the
  warm environment and package options, one process at a time. Do not rebuild
  Mathlib, clear artifacts or create a second warm cache.
- Hot-main and dependency integration remain with their coordinating owners.
  Do not reset peer worktrees, interrupt builds, merge main or change pins.

## Other owners and coordination

Main was observed at `80bc49d17e833795fba00bfeaf1bd053649c4070`.
All required #8826 checks pass. The #8798 book checks pass and its Lean build
remains pending. Their model and dependency integration remain separate from
this group's fixed QICLean pin. Boundary #8849 has passing checks; scanner
#8834 has passing Lean/policy checks with rendering separately tracked.

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
Its owner reports the completed source checks; full PR checks remain separate. Compression owns the
future isolated TNLean integration after that source is fixed. The physical
output and discarded-register protocol producer is still unidentified.
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

The [latest ownership relay](https://github.com/LionSR/TNLean/issues/8769#issuecomment-6048586138)
records the separate analytic QICLean and compression TNLean integration
responsibilities. Check coordination approximately every thirty minutes and
before each new claim or shared-interface change. Public issue coordination
is authorized. Use a small team with disjoint ownership and continue the
active goal while reporting unfinished mathematics accurately.
