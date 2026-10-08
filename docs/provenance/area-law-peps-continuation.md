# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md). The goal
remains active; both source-faithful headline theorems remain unproved.
Twenty-six geometric contributions contain **154 canonically verified
original declarations**. Earlier exact revisions and evidence remain below.

## Current verified source

The exact mathematical source is
`7a9d7f716a443c76f66c2f973575854014166a3b`, on
`feat/area-law-auxiliary-fan-geometry`. Its completed parent is draft
[#8913](https://github.com/LionSR/TNLean/pull/8913), evidence
`d7f49227375497d51de3b8c7395e632076cd0031`, mathematical source
`ba085d83ba7568a8333d4163f05d9711b9a2d71d`.

Four originals establish nonempty interiors and regularity of actual fan
triangles, constant maximum-norm base distance, exclusion of the four allowed
center lines from all-midpoint triangle interiors, and exact concentric
restriction. The first two proofs are extracted or exposed unchanged.
Exactly two old regularity calls and three CellFans calls change names;
all old public signatures and original notices remain retained.

The locked targeted Geometry build passed in **39.464 seconds** and the
fourteen-name imported audit in **7.045 seconds**, without diagnostics.
The reports use only `propext`, `Classical.choice` and `Quot.sound`, or a
subset; CellFanSlot requires no axioms. Strict promotion, deterministic
completion and the sole unchanged **315-record** normal policy pass:
four originals, exactly ten old whole-file refreshes, and **301 immutable
parent records**. All **160** recursive historical files, seven policy/pin
files and twelve frozen mathematical files retain their bytes.

Four failed source attempts and their logs are preserved. They exposed
only elaboration errors in the two new modules. The concentric proof then
compiled; an isolated convex-hull subproof resolved the last sector error.
The successful final revision has one canonical build and one imported audit;
no successful compiler or normal-policy command was repeated. The scoped
timing check records CellFanSectors at 25 seconds, at the warning threshold
and below the 50-second limit. Artifacts are under
`/tmp/tnlean-8758-auxiliary-fan-geometry-`. Full CI and compiled-book checks
remain separate.

## Verified contributions

| Contribution | Publication | Exact proof source | Evidence |
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
| Within-fan contacts and finite fine-cell cover of primaries | [#8897](https://github.com/LionSR/TNLean/pull/8897), evidence `a4833852f7e6dbee5930b1c983fff39e3a74daa7` | `26dbf77709501643284144f4294c4d768966958b` | [combined fan/primary evidence](evidence/8758-fan-primary-contacts.md) |
| Boundary contacts of actual fan triangles | [#8899](https://github.com/LionSR/TNLean/pull/8899), evidence `3847e691d456f820d306b3b58fdfa575f64d75f1` | `9dce097b1d70dff4a59a8a3ed0fb035c725166ac` | [fan-side evidence](evidence/8758-fan-side-contacts.md) |
| Positive-length interfaces of belt runs with primaries and other belt runs | [#8901](https://github.com/LionSR/TNLean/pull/8901), evidence `d6f8fca2f3420463d833fe2b21918edf64a6c677` | `3a65bd3f6b2a0c7ebbc7f198a33edf47aa8d891a` | [belt-run interface evidence](evidence/8758-belt-run-interfaces.md) |
| Dummy interfaces of actual fan triangles and belt runs | [#8902](https://github.com/LionSR/TNLean/pull/8902), evidence `aeae9a15b7d6a745676b04fda477e36e671e1cc2` | `d5463154269cf320c7a176349b64589388220a0e` | [dummy-run interface evidence](evidence/8758-dummy-run-interfaces.md) |
| Actual initial-region identifiers, closed coverage and translated origin | [#8904](https://github.com/LionSR/TNLean/pull/8904), evidence `f93aec9cd0c6ae5dd399f44edd0d0d1e69d364e1` | `afb83051377658183c94673c0c2bd5a2f508a4d3` | [initial regions and origin](evidence/8758-initial-regions-origin.md) |
| Disjoint initial interiors, lattice-free boundaries and unique initial lattice assignment | [#8906](https://github.com/LionSR/TNLean/pull/8906), evidence `aa2dea58b6945af6ca0d3a1c88b89ade7fbf0d03` | `ff3ac34d661f011020c566dff01eed0fb6454881` | [initial lattice partition](evidence/8758-initial-lattice-partition.md) |
| Colors and regularity of actual initial regions | [#8907](https://github.com/LionSR/TNLean/pull/8907), evidence `74d88251d951ced6bdb4b9fdbc251c84e20b5aaf` | `eb7f6c0b9cb30358c0c5125aca3dba7ee56916ac` | [initial interfaces and regularity](evidence/8758-initial-interfaces-regularity.md) |
| Primitive fan frontiers and near-mark mesh/dummy separation | [#8909](https://github.com/LionSR/TNLean/pull/8909), evidence `707599e38a39a3c489daa68804a10879e3073bd0` | `8f86fd6d2e20a77f6c130274cbaad6c5b9f3a60e` | [fan frontiers and near-mark geometry](evidence/8758-fan-frontiers-near-mark.md) |
| Whole square sides and nearby actual initial frontiers | [#8913](https://github.com/LionSR/TNLean/pull/8913), evidence `d7f49227375497d51de3b8c7395e632076cd0031` | `ba085d83ba7568a8333d4163f05d9711b9a2d71d` | [initial star frontiers](evidence/8758-initial-star-frontiers.md) |
| Regularity, base radius, open sectors and concentric restriction | Canonical source verified; draft publication follows completed evidence | `7a9d7f716a443c76f66c2f973575854014166a3b` | [auxiliary fan geometry](evidence/8758-auxiliary-fan-geometry.md) |

## Mathematical obligations that remain

The actual initial family has closed-plane coverage when Z is nonempty,
pairwise disjoint open interiors, lattice-free frontiers at (√2,√3), unique
initial membership at each integer site, opposite colours across shared
nondegenerate segments, and birth-region regularity. The ambient identifier
family is countable. The near-mark frontier estimate and four fan results
supply the next local assignment argument.

The next obligations are:

1. Derive the actual local sector assignment, merge inactive rays, and prove
   the full isolated-star description with the incident scales.
2. Construct simultaneous recursive deletion and replacement, including the
   actual descendants and repaired regions.
3. Prove clearance from the cut and earlier same-colour templates, and control
   exceptional residual boundaries.
4. Restrict to the finite lattice region and prove the nonempty finite ordered
   two-family partition, compatible templates and scales, and ∑ᵢ nᵢ⁻¹⁰⁰ ≤ C b.

The existing counting, separation, absorption and auxiliary series results
remain local ingredients. The source proposition assumes b>0; no verified
b=0 reduction is supplied. The full two-family proposition, area-law theorem
and polynomial PEPS theorem remain open.

## Next claimed sources and immediate action

Actual eight-sector assignment is claimed at
[#8758, comment 6051085776](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6051085776).
InitialSectorAssignment.lean is independently approved at raw SHA-256
`434d5724900a52ade60054a461e2d7248eab9bec0fd8fc7047985bacfc571f09`.
Its 280-line proof derives the unique assignment from eight working open
triangles of half-side t/32 to actual initial identifiers. For every identifier,
including those assigned no triangle, the birth region in the closed t/64
square equals the union of its smaller assigned triangles. Endpoint
nonemptiness and the lower exponent are derived from actual memberships.
No sector or desired boundary description is assumed. Compilation is pending.

Its scoped chapter and unbound preparatory metadata are independently
approved. After publishing the current completion, capture that clean parent
once and measure its actual row, ledger and recursive-history counts. The
prospective counts are 315/30/164; they are not a future capture. Then assemble
only the released assignment source, chapter, audit and metadata, bind the
actual revisions and perform the first canonical check. No old row requires
refresh. The prospective single original gives 316 records and a five-file
mathematical freeze.

The adjacent-color bridge is separately claimed at
[#8758, comment 6051321426](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6051321426).
InitialSectorColors.lean is independently approved at raw SHA-256
`926315c43904f64559dd150937971d4b7f110a9a991e2dfa62b2b2630a55d4e1`.
The 139-line proof derives equal colors iff equal assigned identifiers for
actual neighboring sectors, using their nondegenerate common radial segment.
It does not identify separate nonadjacent sectors. Its scoped chapter is
approved; source compilation remains pending. Keep it outside the assignment
contribution's five-file freeze.

The later run-component and no-active case have a read-only design at
`/tmp/tnlean-8758-actual-sector-runs-scout.md`, SHA-256
`3cb53c80733ab8877ba2688ac50deab0d25098b510bc9f78faf4b1c1f046517a`.
Existing run components and reachability supply the mergers without another
cyclic proof. The two local run results are now claimed at
[#8758, comment 6051518645](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6051518645).
Only the new run source may be prepared. The existing centered-square helper
will be exposed unchanged after the assignment contribution is verified and
published; its released bytes must remain untouched until then.

## Worktrees, resources and coordination

`worktrees/area-law-peps-models` is the sole warmed geometry worktree. Its
QICLean pin remains `8d5389d23c8e675a0117442e1a0d2c683a4bad41`; Mathlib
remains at `c55e6e786f49471c72fbddbec5415808896aec1e`, Lean v4.35.0-rc3.
Use its own locked wrapper for compiler or cache mutations. The common lock
waits without consuming CPU. Never rebuild Mathlib from source or repeat a
successful check without a genuine change or unresolved concern.

`worktrees/area-law-source-preparation` has no `.lake`; its preparation HEAD
remains `3847e691d456f820d306b3b58fdfa575f64d75f1`. Released and future sources
coexist there. Copy only explicitly released files, preserving original notices;
do not reset this tree or copy all files. Hot-main and dependency integration
retain their separate owners. No peer build is interrupted.

Coordination for #8733, #8758, #8753 and #8769 was refreshed at 03:23 UTC;
source main independently remains at the pinned manuscript revision.
The latest constructive-interface reply is
[#8769, comment 6051249843](https://github.com/LionSR/TNLean/issues/8769#issuecomment-6051249843).
The earlier analytic exact-freeze reply is
[#8753, comment 6050944463](https://github.com/LionSR/TNLean/issues/8753#issuecomment-6050944463).
Refresh approximately every thirty minutes and before new claims or shared
mathematical interface changes. Use a small team with disjoint responsibilities.

The analytic owner reports further physical-density, label-moment and
five-factor results in QICLean #661–663, and the compression owner reports
common sampling in TNLean #8914. Their exact heads and verification are
recorded in
[#8753, comment 6051474374](https://github.com/LionSR/TNLean/issues/8753#issuecomment-6051474374).
These remain owner reports and do not change this geometry worktree's pin.
The #8754 actual-template mixed-square counting claim
[6051373435](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6051373435)
is separately owned and disjoint from initial-star work. Neither headline
theorem is complete.
