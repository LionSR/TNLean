# Positive-length interfaces of actual belt runs

The two original records have passed exact-source canonical verification
and independent mathematical review.
The complete direct package-option check and independent mathematical review
approve the exact released module. The separate canonical results are recorded
below at the frozen production revision.

The completed parent is the face-contact contribution, draft
[#8899](https://github.com/LionSR/TNLean/pull/8899), at evidence
`3847e691d456f820d306b3b58fdfa575f64d75f1`, with verified proof
`9dce097b1d70dff4a59a8a3ed0fb035c725166ac`. Its immutable baseline measures
all 284 records and all 132 tracked files recursively beneath
`docs/provenance/evidence`. Every parent record, shard, historical file,
policy, license and dependency pin is preserved. The public parent handoffs are
[#8758, comment 6049410354](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6049410354)
and [#8733, comment 6049410607](https://github.com/LionSR/TNLean/issues/8733#issuecomment-6049410607).

## Mathematical statements

Fix an arbitrary origin o, finite endpoint set Z, width C ≥ 2 and initial
layer k₀ ≥ 50,000,000. At every layer choose arbitrary valid belt residues.
No sparse-shift estimate, finite-support or nonempty-endpoint assumption is
imposed. The fans use the actual midpoint masks and the previously constructed
colors. Their runs are the actual connected components joining consecutive
triangles of equal color, rather than supplied region or color certificates.

Let R be a run in an actual belt cell at layer k ≥ k₀. Let Q be the primary
birth region at an arbitrary signed pitch index J and layer h ≥ k₀. If a
closed segment with distinct endpoints is contained in both regions, then
J is a retained primary index. Every constituent triangle of R has color
h+1 modulo two, which differs from the primary parity h modulo two.
Retention is a conclusion. The statement allows k=h, signed indices and
empty or disconnected primaries. Fine/layer/pitch scale inequalities are
derived from existing scale definitions, not added as premises.

For runs R and T in two distinct indexed actual belt cells at layers at
least k₀, a closed segment with distinct endpoints shared by their regions
forces every constituent color of R to differ from every constituent color
of T. No contacting triangle pair, endpoint adjacency, reversed endpoint,
matching slot or selected opposing identifier is supplied as a hypothesis.

The shared segment is infinite. The run triangles form a finite family,
and an actual primary is a finite union of closed nonbelt fine cells with
its specified pitch index. Finite extraction therefore gives a two-point
triangle/cell contact in the first statement and a two-point triangle pair
contact in the second. A constituent intersection that were only a
singleton would be finite; finitely many such intersections cannot cover
the shared segment. The existing triangle/base intersection equalities
reduce these contacts to actual elementary segments. Previously proved local
color rules determine the contacting colors, and color constancy on each
actual connected component extends the conclusion to all constituent
triangles. Belt/nonbelt membership derives indexed-cell distinctness in
the primary argument. No new graph, region or label model is introduced.

Two distinct common points of disconnected unions need not lie in a common
constituent pair or provide their joining segment. The nondegenerate shared
segment is retained as the geometric meaning of a positive-length interface.
The within-one-fan run contact theorem has a stronger two-point premise
because all its triangles contain the same center.

## Manuscript and independence

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The manuscript path is
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
The primary interface cites lines 212–218 and 299–323; the belt–belt
interface cites lines 299–323. These two explicitly scoped local consequences
do not mark the full two-family proposition as proved. The proofs are
original and reuse no upstream Lean source or proof text. OpenAI Codex (GPT-6)
assistance is disclosed separately from attribution.

The public assignment is
[#8758, comment 6049314635](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6049314635).
The original notice IDs are
`8758-tnlean.peps.arealaw.geometry.belt_run_primary_interface` and
`8758-tnlean.peps.arealaw.geometry.belt_runs_interface_colors`.

## Released source and independent review

| Module | Public declarations | Released SHA-256 | Direct check |
| --- | --- | --- | --- |
| `BeltRunInterfaces.lean` | `beltCellFanRun_primary_interface`; `beltCellFanRuns_interface_colors_ne` | `855e8f2eedf724e372e752018d3f75e9b4ea41cc35bb02c870f7474eed3b2bde` | Exit 0, no diagnostics; real 12.02 s, user 2.33 s, system 5.47 s |

The released module has 209 lines. Independent complete mathematical review
approves both statements and proofs at that exact hash. The final direct
check is recorded in `/tmp/tnlean-8758-belt-run-interfaces-direct-3.log`,
SHA-256 `eab7ba6972771d4e4144ba64ab268fe11918f87dc2140265d0b63a3cee4d86de`.
This hash precedes original-notice insertion. The subsequent five-file freeze
binds the production module, imported report and mathematical chapter to the
exact source revision recorded below.

## Exact-source canonical verification

Frozen source: `3a65bd3f6b2a0c7ebbc7f198a33edf47aa8d891a`. Completed parent: draft
[#8899](https://github.com/LionSR/TNLean/pull/8899), evidence
`3847e691d456f820d306b3b58fdfa575f64d75f1`, with verified proof
`9dce097b1d70dff4a59a8a3ed0fb035c725166ac`.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Passed, exit 0 | 19.471 s | `b4b6a35012f3952e36c3159874de0801eaee052c404edaec3bba92baf2b84617` |
| Imported two-name report | `lake env lean docs/provenance/evidence/8758-belt-run-interfaces-axioms.lean` | Passed, exit 0 | 4.618 s | `669d357bd5b12c79b5950474a21f22de608a3038226d321f611216aae7ddeff0` |

Both raw logs retain exact revision, command, elapsed-time and exit-code
headers and contain no diagnostics. The imported report contains exactly two
quoted declarations, each depending only on propext, Classical.choice and
Quot.sound. The production module, Geometry aggregator, report, mathematical
chapter and parent chapter retain all five frozen byte sequences.

Strict promotion and the unchanged normal policy pass all 286 records.
Exactly two original rows are added. All 284 parent records and shards,
and all 132 tracked historical evidence files, remain unchanged; no old
declaration is reverified. Only the two new rows' historical preparation
descriptions clarify that canonical verification was pending before source
freeze. The finalizer compares raw promotion to the committed planned rows
and requires its finalized output to equal the normal-policy production shard.
All policy, license, dependency and toolchain bytes are unchanged.

Source synchronization passes with `total_blueprint_refs = 20234` and
20,240 lines in `blueprint/lean_decls`, complete reverse coverage and no
missing, stale or duplicate references. Generated imports cover
2,858 production modules in
75 files. The scoped chapter contains two
theorems and two proofs, with four completion markers. Independent review,
formatter idempotence, reader prose, module guards and pattern checks pass.
The approved pre-notice direct check remains 12.02 seconds wall, 2.33 seconds
user and 5.47 seconds system time; its released SHA-256 is retained above.

Full CI and compiled book checking remain separate. The historical local
whole-library declaration check encountered missing
`TNLean/MPS/Examples/Fibonacci.olean`; that prior evidence and limitation
remain unchanged. QICLean stays pinned to `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

## Further geometric obligations

An interface with the initial dummy neighborhood still needs a separate
whole-side containment argument from an open elementary contact and a shared
nondegenerate segment for run regions. Global region and label assembly,
local sectors, isolated stars, recursive repairs, descendants, the full
two-family proposition and both headline PEPS/area-law theorems remain open.
The contribution proves only the two stated positive-length local color
consequences for the existing actual runs.
