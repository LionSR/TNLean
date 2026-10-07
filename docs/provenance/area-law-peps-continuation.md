# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md).
Last coordination refresh: October 7, 2026, 22:06–22:20 UTC.
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
| Common side endpoints, actual elementary matching and opponent existence | `feat/area-law-actual-side-matching`, based on #8876 | `93c807b97f45312bab807ba47abb06f11d686f18` | [matching and opponents](evidence/8758-actual-side-matching.md) |

These thirteen contributions contain 109 distinct verified declarations.
The current-policy collection has 270 rows; the original planned root row
remains planned. The latest four new declarations and five unchanged prior
statements have exact-source canonical build and standard Lean kernel evidence.
All other 261 parent entries and all 47 historical evidence files are unchanged.
The five CellContacts/DummyCorners records have fresh verification because their
complete source files now use the common endpoint lemmas. Their original
verification at 0ac139a04b8d2519f1199bfe8e2f78a5f1fd63c2 remains preserved.

At frozen source 93c807b97f45312bab807ba47abb06f11d686f18, the Geometry
build passed in 35.475 seconds and the nine-name imported audit in 4.101 seconds,
without warnings. Only three new modules, two refactored callers and their
aggregator compiled. Prebuilt Mathlib and existing TNLean artifacts were reused.
Complete source synchronization passes with 20,224 distinct public references
and 20,218 flattened declaration records. The new chapters contain three
mathematical statements, four declaration records and three proof tags.
Generated imports cover 2,851 production modules in 75 files. Independent
mathematical review approves every new statement and proof, and all five old
public signatures are unchanged. Do not repeat successful canonical checks
merely because work resumes.

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

## Claimed successor and next action

[Opponent uniqueness](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6047895365)
is claimed in a new ElementarySideOpponentUniqueness.lean module. With exactly
the existence hypotheses, prove a unique tag in Option (ℕ × (ℤ × ℤ)) whose
closed region contains the whole segment. The dummy tag denotes Nₖ₀; an actual
fine-cell tag must have h ≥ k₀ and differ from the reference pair. Use actual
disjointness and midpoint geometry; do not supply uniqueness as a premise.

The [claim extension](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6047933668)
promotes the existing private elementary-edge geometry unchanged as
cellFan_elementary_geometry, with two existing callers renamed and no alias.
This shared statement avoids repeating the endpoint argument. It and the
unique-opponent result will be the next two exports. The existing opponent
existence theorem will receive fresh complete-file verification; the other
269 completed parent rows and historical evidence must remain unchanged.
The prospective three-name audit and strict metadata helper are prepared in
/tmp, with source and completed-parent bindings still pending.

The author owns only the new uniqueness module and now has the sole direct
Lean check slot. Root owns the promoted old module, imports and metadata.
The current frozen source and nine-name audit exclude all successor changes.
Once the new proof is released, independently review exact hypotheses, bind
the completed parent baseline, then freeze and verify one combined contribution.

Actual-cell uniqueness is distinct from a primary identifier. For a nonbelt
opponent, the existing unique-primary theorem supplies its primary identifier.
Consistent global labels, actual run identifiers, active interfaces and local
sectors remain to be constructed. Reuse the existing affine-mesh supporting-line
clearance. Recursive repairs, descendant estimates, isolated stars, the full
two-family proposition and both headline theorems remain open.

## Worktrees and verification discipline

- worktrees/area-law-peps-models owns feat/area-law-actual-side-matching and
  the group's only warm cache. Its canonical build/audit are finished and the
  shared lock is released. Metadata changes preserve every frozen production,
  audit and new blueprint byte. Preserve all toolchain and dependency pins.
- worktrees/area-law-source-preparation has no .lake and is on
  feat/area-law-unique-side-opponents. It holds the untracked successor and
  the tracked private-lemma promotion. Preserve both when adopting completed
  evidence. Never include an unfinished successor in generated imports or
  the current audit.
- Canonical builds and cache mutations use the worktree's own locked wrapper.
  The shared kernel lock waits without consuming CPU. Direct source checks
  use the warm environment and package options, one process at a time.
  Do not rebuild Mathlib, clear artifacts or create a second warm cache.
- Hot-main and dependency integration remain with their coordinating owner.
  Do not reset peer worktrees, interrupt builds, merge main or change pins.

## Other owners and coordination

Main was observed at 77e54369696d9a041ec4f16c46c37988a3e2d065. Template
integration #8798 (077f62c33) and boundary integration #8826 (2ed6f6ed) retain
model cd7271b9 and QICLean 83fdc804; book checks pass and Lean builds run.
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

Compression retains #8864, #8866, #8868, #8869 and #8872. Its latest published
head is c54eb4d685ada6d4f69e2e3dcf81960ec1998027, mathematical source
8689eafdd, for actual selective preparation and common finite source-gate data.
The owner now reports 55 checked chronological-expansion declarations and a
nine-declaration fixed-slot producer, with original source occurrences and
exact operator/density identities. Actual source-contraction density and
original-branch selectors remain active. The physical/discarded-register
protocol producer and local tensor-network construction are separately
[queried](https://github.com/LionSR/TNLean/issues/8769#issuecomment-6047613493),
as is additive integration with lifetime/position-cost results and QICLean
#567–571. These owner-reported developments are not a full compression theorem.

The analytic group retains QICLean #618, #621, #622, #624–627 and actual
high-label selection. The high-label source 89941482 reportedly passes a full
9,713-job build, eleven standard reports and four provenance shards; book
rendering remains pending. The actual selected sequence has inverse-polynomial
mass and log dimension k S(ρ) + o(k), including singular densities. Prevector
properties hold eventually; finite small-index repair is underway to obtain
all positive indices with the same asymptotic sequence. No completed all-index
prevector, physical tail estimate, inverse-metric comparison or headline theorem
is claimed. Latest QICLean main 8b9b4bcd and #627 check statuses are reported by
that owner; no dependency pin changes here. The
[coordination refresh](https://github.com/LionSR/TNLean/issues/8753#issuecomment-6047838550)
confirms no overlapping analytic implementation.

Check coordination approximately every thirty minutes and before each new
claim or shared-interface change. Direct cross-thread replies are unavailable;
public issue coordination is authorized. Use a small team with disjoint
ownership. Continue the active goal without routine permission requests and
report unfinished mathematics accurately.
