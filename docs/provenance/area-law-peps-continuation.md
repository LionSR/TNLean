# Continuation record for the area-law and PEPS formalization

This record supports the [continuing goal](area-law-peps-goal.md). The goal
remains active; both source-faithful headline theorems remain unproved.
The 27 geometric contributions contain **155 canonically verified originals**.
The first 26 are published; sector assignment has passed canonical
verification, strict promotion, deterministic completion and normal policy.
Final independent evidence review has passed; draft publication remains pending.

## Current source and completion status

The exact assignment source is
`eec1eadc03a5804a6b526d85f116a140b67fb83e`, on
`feat/area-law-initial-sector-assignment`. Its completed parent is
[#8918](https://github.com/LionSR/TNLean/pull/8918), evidence
`0fb8197b9b45dde8d4aaad8ab03ccfe7d2612015`, mathematical source
`7a9d7f716a443c76f66c2f973575854014166a3b`.

The theorem derives a unique assignment of eight open working sectors of
half-side t/32 to actual initial identifiers. For every identifier, including
one assigned no sector, its birth region in the closed t/64 square is exactly
the union of the smaller assigned closed triangles. Endpoint nonemptiness
and the lower exponent are derived from actual cell and mark memberships;
no desired sector or boundary description is supplied.

The locked Geometry build passed in **18.827 seconds** (assignment leaf:
12 seconds). Its single imported report passed in **4.676 seconds**, without
diagnostics and with exactly `propext`, `Classical.choice` and `Quot.sound`.
The clean parent was captured once: **315 records, 30 ledgers and all 164
recursive historical evidence files**. The one new original gives
**316 records**, with no old refresh and all **315** parent records and **164**
historical files retained. Strict promotion passed in **35.993 seconds**;
deterministic completion passed. The sole normal policy check passed all
316 records in **22.002 seconds**. Five mathematical files and two
reader-checker files are frozen. Guarded finalization and independent final evidence review have passed;
draft publication remains pending.

The first source `a5137f3071e1a7702b77071aaeae78aee9cafdae` failed after
**18.269 seconds** on `Metric.closedBall_prod_same`; no imported report ran.
Source `c28d731278fd8c115ccf507f5dd9579e20046f81` built in **31.849 seconds**
and passed its standard-three report in **17.349 seconds**, with three unused
simplification arguments. Their removal justified the final source check.
All earlier logs and freezes remain retained. No same-revision compiler
check was repeated.

The pre-staging prose check omitted the untracked assignment source, and
its failed committed result was inspected after compilation began. A full
comparison also rejected required public-claim notice fields in four #8918
modules. The earlier prose-success claim was incomplete; #8918's sound
mathematical checks are unaffected. The reviewed checker correction permits
only this exact field in a complete original notice. Ten focused tests
passed in 0.041 seconds. Successful prose, import, coverage and formatting
checks remain applicable after the proof-only three-argument cleanup.

The first strict helper failed before any output or production-shard write:
two historical JSON reads received strings instead of paths. Its retained
record gives exit 1, without a measured elapsed time. A separate fourth
helper draft preserves the third draft, corrects these two arguments and
records the failure. Independent review approved the correction and the
failed strict step then passed. The mathematical compiler was not repeated.

Full CI and compiled-book checks remain separate. The known unrelated local
missing-Fibonacci declaration-check limitation is retained. Current artifacts
are under `/tmp/tnlean-8758-actual-sector-assignment-`.

## Verified contributions and publication status

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
| Regularity, base radius, open sectors and concentric restriction | [#8918](https://github.com/LionSR/TNLean/pull/8918), evidence `0fb8197b9b45dde8d4aaad8ab03ccfe7d2612015` | `7a9d7f716a443c76f66c2f973575854014166a3b` | [auxiliary fan geometry](evidence/8758-auxiliary-fan-geometry.md) |
| Unique actual local sector assignment | Canonical, promotion and normal policy passed; publication pending | `eec1eadc03a5804a6b526d85f116a140b67fb83e` | [actual sector assignment](evidence/8758-actual-sector-assignment.md), independently reviewed |

## Mathematical obligations that remain

The actual initial family has closed-plane coverage when Z is nonempty,
pairwise disjoint open interiors, lattice-free frontiers at (√2,√3), unique
initial membership at each integer site, opposite colours across shared
nondegenerate segments, and birth-region regularity. The ambient identifier
family is countable. The local sector assignment has passed canonical source,
promotion and normal policy checks, is independently reviewed and awaits draft publication.

The next obligations are:

1. Complete the assignment contribution, derive adjacent-sector colours and
   inactive-ray runs, identify active frontiers, and prove the full isolated-star
   description with the incident scales.
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

Publish the independently reviewed assignment claim
[6051085776](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6051085776)
before publication. The original source and scoped chapter remain in the
retained history. No parent is recaptured and no old row is refreshed.

The adjacent-colour bridge is claimed at
[6051321426](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6051321426).
Its approved 139-line source, raw
`926315c43904f64559dd150937971d4b7f110a9a991e2dfa62b2b2630a55d4e1`,
derives colour equality exactly when assigned identifiers agree for neighboring
sectors, without classifying nonadjacent sectors. The one-original Colors
package is independently approved, unbound and uncompiled. Its separate
single-thread audit revision is
`/tmp/tnlean-8758-initial-sector-colors-audit-j1-revision-3/`.
The exact future audit uses `lake env lean -j1`; no result is inferred from
the separately reported ENFILE remedy. Parent capture follows publication.

The run/no-active case is claimed at
[6051518645](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6051518645).
The approved unbound Runs package, raw
`77da4f6517ee992591a3f7982b98701d5d9eb04483ee48ead4d5775b1d2c0a55`,
contains two run results and unchanged public exposure of the centered-square
identity. Precisely the old assignment
row would receive a later whole-file refresh: four reports and seven frozen
files. The parent must be the completed Colors publication. It changes no
current assignment source before that publication.

The ActiveRays contribution is claimed at
[6052058387](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6052058387).
Its unbound package is being prepared: two frontier equivalences and unchanged
public exposure of the finite-cover frontier argument, plus precisely one
old FanFrontiers refresh. The open radius is t/64; the closed restricted
radius is t/128. A realized minimum incident witness later identifies t with
its actual side. Corrected prose-only raw source is
`c30091d692e785a7ed87b10bcb3849028f13144f9c7a361c9d28ce48d93a39ef`;
the earlier raw is archived, and the corrected chapter is independently
approved. No finite global identifier family or complete isolated-star
assertion is assumed. Binding and capture await the preceding publications.

Colors, Runs and ActiveRays retain unset parent/source bindings and have no
compiler or provenance-completion result. None is included in the count.

## Worktrees, resources and coordination

`worktrees/area-law-peps-models` is the sole warmed geometry worktree. Its
QICLean pin remains `8d5389d23c8e675a0117442e1a0d2c683a4bad41`; Mathlib
remains `c55e6e786f49471c72fbddbec5415808896aec1e`, Lean v4.35.0-rc3.
Use its locked wrapper. The common lock waits without CPU use. Never rebuild
Mathlib from source or repeat a successful same-revision check without an
unresolved concern. The source-preparation tree has no `.lake`; copy only
released files and retain notices. Do not reset it or copy every file.
Hot-main and dependency integration retain separate owners; no peer build
is interrupted. Imported reports are serialized; the explicit `lean -j1`
remedy addresses the separately reported ENFILE failures.

Coordination for #8733, #8758, #8753 and #8769 was refreshed at **04:41 UTC**.
The manuscript remains pinned to
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Latest observed replies are
[#8769, comment 6052126530](https://github.com/LionSR/TNLean/issues/8769#issuecomment-6052126530)
and [#8753, comment 6052011934](https://github.com/LionSR/TNLean/issues/8753#issuecomment-6052011934).
Refresh roughly every thirty minutes and before new claims or changes to
shared mathematical assumptions. Responsibilities remain disjoint.

The later native analytic owner reports QICLean #672 at
`5c5a5068d5bb5ef1f2571593dcf17d68ad86449d` (signed centered Schur comparisons)
and #673 at `d949d2dc7dec1872aa4838d374dbe47512ae4919` (actual five-operator
Hölder). Reported full builds contain 9,825 and 9,826 jobs; reported books
have 473 pages and 3,771/3,774 native references, respectively. Imported
audits are owner-reported, with no exact foundation-count inference here.
The independent-copy and two recurrence refactors, reported at prefix
`5ac8f085`, were mathematically reviewed by that owner and await its canonical
verification. These are owner reports, not adopted geometric evidence or
pin changes. The compression owner's #8924 head is reported as
`fc51aab88de42b6bf3ad335328197a0b1f433f2f`; its source and verification are
not adopted here. Physical output, analytic integration and PEPS compression
retain their existing owners. Both headline theorems remain unfinished.

The separately owned counting draft
[#8919](https://github.com/LionSR/TNLean/pull/8919) has a queued compatible-cache
review after this assignment is complete, accepted in comment 6052058387.
Read-only preflight found the requested head
`f8fb4c28f91c4c0bcc63581449d81b8fcc71a441` superseded by observed
`cb67e588d7da3820109dcdd0dad4a1b79d19d3c3`, with two proof-body corrections.
Pins and package options agree; five common imported files are byte-identical
and eight required modules are absent from the geometry cache. At 04:11 the
checks were action-required, with none verified. Fresh exact-head and CI
coordination precede the narrow compatible target, strict regression and
fourteen-name audit review, avoiding any already completed check. The observed
head is not adopted automatically, and the obsolete source will not be
compiled. Source correction, promotion and integration remain with the
counting owner. The exact plan is
`/tmp/tnlean-8919-compatible-review-plan.json`.
