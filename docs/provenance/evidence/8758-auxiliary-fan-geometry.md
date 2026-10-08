# Regularity, radius and restriction of actual dyadic fans

Canonical source verification has passed without diagnostics.

Exact source: `7a9d7f716a443c76f66c2f973575854014166a3b`. Completed parent evidence: `d7f49227375497d51de3b8c7395e632076cd0031`.
The completed immutable parent capture measures 311 entries in 29 ledgers and all 160 recursive historical evidence files.

## Mathematical scope

Every actual fan triangle has nonempty interior and equals the closure
of that interior.
The origin, natural dyadic exponent, signed cell index and optional midpoint
choices are arbitrary. Every point of an elementary base has maximum-norm
distance 2^ell/2 from the center. The determinant and fan-regularity proofs
move unchanged to FanRegularity; the private base-radius theorem becomes
public unchanged in CellFans. Precisely two old regularity calls and three
CellFans calls are renamed, with no old public signature or notice changed.

In the fan with all four midpoint subdivisions, every open triangle misses
all four allowed lines through its center. A surjective-functional argument
places its interior in the strict half-plane determined by the actual
vertices. No region assignment or boundary exclusion is assumed.

For two concentric actual fans of exponents ell and ell+1, use the same
optional subdivision and corresponding elementary position. Put r=2^ell/2,
with origins c-r(1,1) and c-2r(1,1), respectively, and cell index zero.
The larger triangle intersected with the closed maximum-norm ball of radius
r equals the smaller triangle. The factor-one-half homothety and actual
base radius give both inclusions.

## Source and independence

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 299–323, especially
308–316, and `geometry:initial-stars`, lines 333–370, especially 352–363.
The exact path is
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
[Pinned manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L352-L363).
The manuscript prescribes: “Join the center of each belt cell to the
endpoints of its elementary segments.”
[Exact manuscript, lines 308–310](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L308-L310).
Public assignment: [#8758, comment 6050817719](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6050817719).

No upstream Lean source or proof text is reused. The extracted arguments
already belong to TNLean. Original attribution, Apache notices, stable
identities, earlier verification and every historical file remain retained.
OpenAI Codex (GPT-6) assistance is disclosed separately from attribution;
submission and human review responsibility remain with the maintainer.

## Independent mathematical review

| Module | Approved raw SHA-256 | First check at prepared source |
| --- | --- | --- |
| FanRegularity | `2e1c30f312f7bb1e5866bb80e4fcf143d075d6eef9946ad0703d98b96e06e131` | Combined canonical build |
| CellFans | `63618634a67ec019d5801334b39ecbd90bbe10db814d0b15cd3363724c1c7ae6` | Combined canonical build |
| CellFanSectors | `77e45d9f6ce72a8bbb9a7c2e6522e8b8c668f3ce36dce2b41450ec3540967365` | Combined canonical build |
| ConcentricFans | `00b5058cb4e16c18b2d6b5a27cc500bd8e7e77f245c528797c9fe3c80525d392` | Combined canonical build |
| InitialRegionRegularity | `b92e1d96598a75282df27ffbb3abeb6d1a8a7be396486d325115943b7e2aa30f` | Combined canonical build |

Complete mathematical reviews approve the statements, proofs and exact
extraction. These raw hashes precede original-notice insertion and formatting.
No direct production-module log, timing or elaboration success is inferred.

## Exact-source verification

The first canonical attempt at `1e3d60b0ba3114a5c36fd1feb0a73508803e5ed0` failed after 58.878 seconds, before any imported audit. The failed driver and build logs are retained with SHA-256 `a79b2fb9a687ec2372c4c0b7a8912ea5456f4acb5a0bcc0ca892e47b39a7b7fe` and `c4a630b94a5b8388497870e9c79a0fbf6eb2a69b21dd04fbcb3150a6eed8ad83`, respectively. The failed freeze and helper bindings are preserved. The corrected source changes only elaboration corrections in the sector module and four endpoint-identification lines in the concentric proof. Its sole canonical check reuses successful dependencies; no direct check or successful canonical command is repeated.

A second canonical attempt at `544e6d7254c313c54879a40e245e7660434ae06d` failed after 28.256 seconds. The concentric module compiled without diagnostics; only the sector module still failed. No imported audit ran. Its failed driver and build logs retain SHA-256 `136f6c3336dfb80bfea2f7238341fab8d62be786847b655dca3733d27f346f27` and `130a12c524238a326ab0859db70ade7f9dc97fcdec0556fc2feea706e1387198`. The final correction supplies the real half-plane target explicitly and chooses arithmetic branches explicitly. Earlier successful dependencies remain cached.

A third canonical attempt at `6891825345c5adeebd333ffc7d4a763027b553bc` failed after 24.577 seconds, before the imported audit. Arithmetic cases closed; the first vertex required an explicit real reflexive inequality, and two redundant tactic forms were removed. The failed driver and build logs retain SHA-256 `01022f87218ce9a38dd1c51b8f8507ef26ed90481fe642692a6a97e676c98560` and `743911a7dd7400533ef32b3931d320b4b6c2f53ea978f347eb0aa2fbcefb5034`. The corrected source retains every public statement.

A fourth canonical attempt at `1399ea2519640d4fcbc63dcea91dc1770245f365` failed after 44.487 seconds, before the imported audit: the vertex case split removed the point named in its explicit annotation. The failed driver and build logs retain SHA-256 `0385c0669013b58c873045dd4456631683b3ad9b04ee0d1308591fd94a7db4fa` and `259249aa67f2103e3b1b6d7427edea879619b4e0fcbf298048530e9f3267c06f`. An isolated convex-hull half-plane example then passed under the lock. This checks only that subproof, not the production module. The final two-line correction exposes the real inequality before splitting the vertices.

| Check | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- |
| Canonical Geometry build | Passed, exit 0, no diagnostics | 39.464 s | f840061adc26120d61e99673669aeaf3d5c7d7e44fab2e8ea60fda8d5b3aa65d |
| Fourteen imported kernel reports | Passed, exit 0 | 7.045 s | 5103b284a5def916e5ddbd96283476c6050ae32c906b2a7b6c841a559b78ad5c |

All fourteen exact quoted reports use only propext, Classical.choice and Quot.sound, or a subset of these foundations. Nine existing CellFans records and one existing InitialRegionRegularity record receive fresh source-bound evidence. Their public commands are unchanged after reversing only the authorized helper-call names.

The canonical commands are `lake build TNLean.PEPS.AreaLaw.Geometry` and
`lake env lean docs/provenance/evidence/8758-auxiliary-fan-geometry-axioms.lean`,
run serially under the repository lock in the sole warmed worktree.
Actual logs are `docs/provenance/evidence/8758-auxiliary-fan-geometry-build.log`
and `docs/provenance/evidence/8758-auxiliary-fan-geometry-axioms.log`.

Strict promotion and the unchanged normal policy passed all 315 records: four new originals, ten reverifications and 301 immutable parent records. All measured recursively tracked historical evidence files are byte-identical; no policy, license or dependency pin was changed.
Source synchronization passed total_blueprint_refs = 20263 and 20269 lines in blueprint/lean_decls, with complete reverse coverage.
2873 production modules and 75 generated import files.
Pinned formatting and idempotence, reader prose, module and source guards, independent mathematical review and the scoped pattern review passed. The ledger records unchanged determinant/fan regularity extraction, base-norm promotion and their exact existing callers; the four approved auxiliary results are the only additions.
The timing assessment records this warning: CellFanSectors compiled in 25.000 seconds, at the 25-second warning threshold and below the 50-second limit. No successful compiler check was repeated.

The imported audit includes four new originals and ten existing records
across five modules, including the five CellFans definitions and abbreviations.
The three new chapters contain three theorems and proofs; the existing
CellFans chapter adds only the base-radius theorem and proof. All other
entries of that chapter are retained. QICLean remains pinned to
`8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

All twelve frozen files retain their exact source-revision bytes:

| File | SHA-256 |
| --- | --- |
| TNLean/PEPS/AreaLaw/Geometry.lean | `82c3ebccc8cedfc5679ea513c53e639cb2ae8f6c2706e074e4feb7f6b35184b8` |
| TNLean/PEPS/AreaLaw/Geometry/CellFanSectors.lean | `4f06330faad247bf5c470e7d7d3b4e5276e32a8d0cc3832668950710f57fb98b` |
| TNLean/PEPS/AreaLaw/Geometry/CellFans.lean | `e216a5c02587a668994fef953e7eb3dca0d473ed7bb0689d98238846d1cbd6c0` |
| TNLean/PEPS/AreaLaw/Geometry/ConcentricFans.lean | `89e1c10e539abfaf06b56f282703248c45ecb42d893fef6dbb1e94d73c5a9d8f` |
| TNLean/PEPS/AreaLaw/Geometry/FanRegularity.lean | `e288efd7d09db77da828dae8fec5a15e02512efe11e5ac513c92ab153b84eaa8` |
| TNLean/PEPS/AreaLaw/Geometry/InitialRegionRegularity.lean | `b92e1d96598a75282df27ffbb3abeb6d1a8a7be396486d325115943b7e2aa30f` |
| blueprint/src/chapter/ch24_peps_area_law_cell_fan_sectors.tex | `0c780e155fdd462e3b99f661101766d9826c0cc70a10fea43fd2aee10c545940` |
| blueprint/src/chapter/ch24_peps_area_law_cell_fans.tex | `c84bd54b1a31f02e6f28770bf435a5f8ce22f14752205b6897c53b9d495ff2eb` |
| blueprint/src/chapter/ch24_peps_area_law_concentric_fans.tex | `b5067669dc34fbc744cbc440065c51d104958d76d5584c265cd6452732bf2439` |
| blueprint/src/chapter/ch24_peps_area_law_fan_regularity.tex | `ea331ce52ae05df717055d117274fd63d04e7063596055231c4e7bc73ed1f5a9` |
| blueprint/src/chapter/ch24_peps_regions.tex | `dd3871ca13c34a4b53a76e3ec97ef6eda784962bb93fed6c27869e5960df6a3c` |
| docs/provenance/evidence/8758-auxiliary-fan-geometry-axioms.lean | `9e6a8ae7f673ad6407f1080c671655030c01aa11c07b1783deb9039504ba1e7a` |


## Retained earlier evidence

Only the nine CellFans records and the single InitialRegionRegularity record
receive fresh verification and one fixed appended reuse-history note.
The three NonbeltPrimaries entries sharing the first shard and the earlier
interface entry sharing the second shard remain immutable. Every other
301 parent entry and all 160 recursive historical evidence files
are retained. Raw strict promotion and its deterministic completion output
are distinct immutable artifacts.

| Declaration | Original source | Retained original logs |
| --- | --- | --- |
| TNLean.PEPS.AreaLaw.Geometry.CellFanSlot | 8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2 | docs/provenance/evidence/8758-cell-fans-build.log, docs/provenance/evidence/8758-cell-fans-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.card_cellFanSlot_bounds | 8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2 | docs/provenance/evidence/8758-cell-fans-build.log, docs/provenance/evidence/8758-cell-fans-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.cellFanCenter | 8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2 | docs/provenance/evidence/8758-cell-fans-build.log, docs/provenance/evidence/8758-cell-fans-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.cellFanEnd | 8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2 | docs/provenance/evidence/8758-cell-fans-build.log, docs/provenance/evidence/8758-cell-fans-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.cellFanPolygon | 8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2 | docs/provenance/evidence/8758-cell-fans-build.log, docs/provenance/evidence/8758-cell-fans-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.cellFanPolygons_cover | 8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2 | docs/provenance/evidence/8758-cell-fans-build.log, docs/provenance/evidence/8758-cell-fans-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.cellFanPolygons_inter_eq | 8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2 | docs/provenance/evidence/8758-cell-fans-build.log, docs/provenance/evidence/8758-cell-fans-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.cellFanStart | 8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2 | docs/provenance/evidence/8758-cell-fans-build.log, docs/provenance/evidence/8758-cell-fans-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.cellFan_vertices_mem_beltCellMarks | 8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2 | docs/provenance/evidence/8758-cell-fans-build.log, docs/provenance/evidence/8758-cell-fans-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.initialBirthRegion_eq_closure_initialOpenRegion | eb7f6c0b9cb30358c0c5125aca3dba7ee56916ac | docs/provenance/evidence/8758-initial-interfaces-regularity-build.log, docs/provenance/evidence/8758-initial-interfaces-regularity-axioms.log |


## Further obligations

Full CI and book rendering remain pending. Actual sector assignment, active
rays, isolated stars, recursive repairs, the full two-family proposition
and both headline PEPS/area-law theorems are not established by this contribution.
