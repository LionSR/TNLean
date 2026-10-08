# Whole sides and initial frontiers near an actual mark

Canonical source verification has passed without diagnostics.

Exact source: `ba085d83ba7568a8333d4163f05d9711b9a2d71d`. Completed parent evidence: `707599e38a39a3c489daa68804a10879e3073bd0`.
The completed immutable parent capture measures 309 entries in 28 ledgers and all 156 recursive historical evidence files.
Only the two affected
dummy-interface records receive fresh source-bound verification; the other
307 parent records and every unaffected shard remain unchanged.

## Mathematical scope

Every frontier point of an actual translated dyadic square belongs to one
of its four whole closed sides. The origin, natural exponent and signed
cell index are arbitrary. The existing private product-frontier proof is
moved unchanged to its public owner; only its name and visibility change.

For the actual initial identifiers, let C ≥ 2 and k₀ ≥ 50,000,000, and let
v be an actual mark of an actual reference fine cell at layer k ≥ k₀.
If an actual birth-region frontier point x satisfies
dist(v,x) < 2^(fineScaleIndex k)/32, then x−v has one of the four allowed
directions. No local boundary description, selected ray, sector,
nonempty-endpoint, contact or minimum-scale hypothesis is supplied.

Finite cell and fan decompositions reduce the frontier to actual square
sides and radial segments. Near contact provides the common quarter mesh.
The allowed-line clearance forces the supporting line of a sufficiently
near segment to pass through v. In the dummy case, sixteen-side separation
forces k = k₀ before the coarse-side endpoints are placed on the same mesh.
The assertion retains all actual initial identifiers, including disconnected
primaries and arbitrary finite endpoint sets.

## Sources and proof independence

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 333–370,
especially 352–359. The actual construction is in `prop:two-families`,
lines 154–177, 212–218 and 299–323. The exact pinned manuscript is
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The phrase “common translated” specifies the grids' shared origin.
[Pinned manuscript, lines 299–306](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L299-L306).

The new proofs are original, with no upstream Lean source or proof text
reused. The extracted argument was already part of TNLean. Original notices,
licenses, prior history and every historical log are retained. OpenAI Codex
(GPT-6) assistance is disclosed separately from attribution; submission and
human review responsibility remain with the maintainer.
Public assignments:
[#8758, comment 6050562726](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6050562726)
and [#8758, comment 6050540131](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6050540131).

## Prepared source and independent review

| Module | Approved raw SHA-256 | First source check |
| --- | --- | --- |
| CellSides.lean | `71fe8baa01014a7568bad218fb9bcab0f15ff7a9a062b0452ec14df7b7bd1114` | Combined canonical build; no direct check performed |
| InitialStarFrontiers.lean | `234bcd9e43f00d850a46743b390e671073b7c202c3b321fb078ccf96a86448a8` | Combined canonical build; no direct check performed |
| Revised DummyRunInterfaces.lean | `a2868a8bda7fdd39a29ed46bbb034a4e9eb98b83bbe6bb89fe5aeb6289cac38a` | Combined canonical build at this source; no direct repeat |

Independent mathematical review approves both complete new statements and
proofs, and the unchanged extraction and scoped chapter. The final frontier
argument reuses actual fan-cover and closure containment in its radial case;
the copied endpoint-convexity helper is removed. No direct log, timing or
elaboration success is inferred from mathematical review.

## Exact-source verification

| Check | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- |
| Canonical Geometry build | Passed, exit 0, no diagnostics | 91.799 s | 3ab7a6a5088a5e3d3f7360e149243d8f87c0d254bf81e910a7b5945ec671225b |
| Four imported kernel reports | Passed, exit 0 | 35.527 s | 97a88374859021ca802437efd2b13d17fce0970424df48ae77deb072935ec949 |

All four exact quoted reports use only propext, Classical.choice and Quot.sound, or a subset of these foundations. The two reused dummy-interface conclusions receive fresh source-bound evidence. Their statements are unchanged; only the authorized helper call in the first public proof is renamed, and the second proof is unchanged.

The canonical commands are `lake build TNLean.PEPS.AreaLaw.Geometry` and
`lake env lean docs/provenance/evidence/8758-initial-star-frontiers-axioms.lean`,
run serially in the existing warm worktree under the repository lock.
Actual logs are `docs/provenance/evidence/8758-initial-star-frontiers-build.log`
and `docs/provenance/evidence/8758-initial-star-frontiers-axioms.log`.

Strict promotion and the unchanged normal policy passed all 311 records: two new originals, two dummy-interface reverifications and 307 immutable parent records. All measured recursively tracked historical evidence files are byte-identical; no policy, license or dependency pin was changed.
Source synchronization passed total_blueprint_refs = 20259 and 20265 lines in blueprint/lean_decls, with complete reverse coverage.
2870 production modules and 75 generated import files.
Pinned formatting and idempotence, reader prose, module and source guards, independent mathematical review and the scoped pattern review passed. The ledger records the unchanged whole-side helper extraction and its reuse; no additional public result is introduced.
The timing assessment records this warning: CellSides compiled in 29.000 seconds, above the 25-second warning threshold and below the 50-second limit. No successful compiler check was repeated.
The chapters contain two theorem statements, two proofs and two declaration
tags. QICLean remains pinned to `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

All eight frozen files retain their exact source-revision bytes:

| File | SHA-256 |
| --- | --- |
| TNLean/PEPS/AreaLaw/Geometry.lean | `6b6cba6b90f589d22052137ab1b4912d2f9215e1f671a474433199655cfb16ae` |
| TNLean/PEPS/AreaLaw/Geometry/CellSides.lean | `0c4fb55dc182b8ad2a4a18d1cb7c897dc0415e7191a3d525d970a28466e7d155` |
| TNLean/PEPS/AreaLaw/Geometry/DummyRunInterfaces.lean | `d8235f4de2a2899a11ab7597c528e41c437b9f7455c5400951ba755cfaa15c4d` |
| TNLean/PEPS/AreaLaw/Geometry/InitialStarFrontiers.lean | `ebe915a7b4b3a9ae4b5b5d13b915b62a12ed5bb3a4c49ec4706db7f82377e880` |
| blueprint/src/chapter/ch24_peps_area_law_cell_sides.tex | `bece66619d8dc120832e1043df9aac7735324b6df923b518b61cfb087c308bcf` |
| blueprint/src/chapter/ch24_peps_area_law_initial_star_frontiers.tex | `3c9fe96a6ba1c06eb88ded9f5e71311adec6971b725a01bc1667c6b8d3641f51` |
| blueprint/src/chapter/ch24_peps_regions.tex | `a4507006e5f2082c3a09c2d31c102c1e777aa60e756c533d6a06392ca4caa3f7` |
| docs/provenance/evidence/8758-initial-star-frontiers-axioms.lean | `a75d0de8e981c03fbaa6211eab45856479c257b379fb16a14667de33f6ba6761` |


## Retained dummy-interface evidence

Only the two public conclusions in the revised dummy-interface module
receive fresh verification and one fixed appended reuse-history note.
Their public signatures are unchanged. In the first proof, only one call
to the moved helper is renamed; the strict comparison reverses exactly
that rename. The second public proof is unchanged. The extracted helper's
signature and proof are compared after changing only its name and visibility.
All other 307 parent entries and all 156 recursively tracked
historical files retain their exact bytes. The original ledger and logs
remain available at the completed parent.

| Declaration | Original source | Retained original logs |
| --- | --- | --- |
| TNLean.PEPS.AreaLaw.Geometry.beltCellFanRun_dummy_interface | d5463154269cf320c7a176349b64589388220a0e | docs/provenance/evidence/8758-dummy-run-interfaces-build.log, docs/provenance/evidence/8758-dummy-run-interfaces-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.fineLayer_cellFanPolygon_inter_dummy_eq | d5463154269cf320c7a176349b64589388220a0e | docs/provenance/evidence/8758-dummy-run-interfaces-build.log, docs/provenance/evidence/8758-dummy-run-interfaces-axioms.log |


## Remaining obligations

Full CI and book rendering remain pending. The earlier local declaration
check was limited by the unrelated missing `TNLean/MPS/Examples/Fibonacci.olean`;
no successful full local declaration check is claimed here.

The local allowed directions do not yet assign active rays or sectors.
Isolated stars, simultaneous repairs, residual descendants, their bounds,
finite lattice sampling and uniform summation remain further obligations.
The full two-family proposition and both headline PEPS/area-law theorems
remain unproved by this contribution.
