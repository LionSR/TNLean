# Unique actual sector assignment and closed local restriction

Canonical source verification has passed without diagnostics.

Exact source: `eec1eadc03a5804a6b526d85f116a140b67fb83e`. Completed parent: `0fb8197b9b45dde8d4aaad8ab03ccfe7d2612015`.
The completed immutable parent capture measures 315 entries in 30 ledgers and all 164 recursive historical evidence files.

## Mathematical scope

Fix C ≥ 2, initial layer k₀ ≥ 50,000,000, an arbitrary origin and finite
endpoint set, and arbitrary valid pitch residues at every layer. Let
k ≥ k₀, let z be an actual reference fine-cell index, and let v be any
of its nine actual marks. Put t_k = 2^(fineScaleIndex k),
ℓ = fineScaleIndex k − 5 and r = 2^ℓ/2 = t_k/64.

The eight open all-midpoint triangles of the working fan centered at v,
with half-side 2r = t_k/32, have a unique assignment to the actual initial
identifiers. Each open triangle is contained in its assigned initial
open region. For every identifier, the birth region intersected with the
final closed square of half-side r is exactly the union of its assigned
smaller closed triangles. The union is empty if no sector is assigned.

The actual reference memberships imply that Z is nonempty. The late-layer
bound gives the lower fine exponent needed for the radius calculation.
Neither assertion is a supplied hypothesis. Preconnectedness and frontier
exclusion give the unique open assignment. The finite open fan is dense
in the working square. Initial-region regularity and finite closedness
then give the exact equality for all identifiers, and concentric clipping
passes to the final square. No local boundary description, sector,
active-ray, contact, matching, sparsity or finite-support certificate is
assumed. The ambient initial identifier family remains countable.

## Source and proof independence

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 333–370,
especially 352–370, and the actual identifiers in `prop:two-families`,
lines 299–323. The manuscript states that “Each sector” has one tile
identifier; the present result treats the eight fixed working sectors.
[Exact pinned manuscript, lines 341–345](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L341-L345).
The exact manuscript path is `preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Public assignment: [#8758, comment 6051085776](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6051085776).

No upstream Lean source or proof text is reused. OpenAI Codex (GPT-6)
assistance is disclosed separately from source attribution; submission and
human review responsibility remain with the maintainer.

## Released source and independent review

The complete released source is independently approved by root and
adjacent_scales at raw SHA-256 `434d5724900a52ade60054a461e2d7248eab9bec0fd8fc7047985bacfc571f09` (280 lines).
The scoped chapter is independently approved at
`eb397bb10bd299c9f861cf10d7ebca1146887d3f14fe803c3f49cf658f63dc15`.
The original mathematical review preceded the first failed canonical
attempt. The namespace correction and later removal of three unused arguments
preserve the statement and mathematical argument. The final canonical outcome is recorded in the exact-source verification
section below. No direct compiler log, timing or success is inferred from
mathematical review.

## Preserved failed attempt and reader-check findings

The first canonical Geometry build at
`a5137f3071e1a7702b77071aaeae78aee9cafdae` failed after **18.269 s**.
The private centered-cell identity used the nonexistent qualification
`Metric.closedBall_prod_same`; the corrected source uses
`closedBall_prod_same`. No imported report ran at the failed source.
The namespace-corrected raw source has SHA-256
`6c094b8937e36ee5094f13047160876c7f510f97e8a94b910a2760f444410ea0`.
The original notice is unchanged, and the original released raw source
`434d5724900a52ade60054a461e2d7248eab9bec0fd8fc7047985bacfc571f09`
remains part of the preparation history.

The second source,
`c28d731278fd8c115ccf507f5dd9579e20046f81`, built successfully in
**31.849 s** and its single imported report passed in **17.349 s**, using
exactly `propext`, `Classical.choice` and `Quot.sound`. The build reported
three unused simplification arguments: `Prod.fst`, `Prod.snd` and
`Int.cast_one`. No provenance promotion was performed at that source.
The released cleanup removes only those three arguments; its raw SHA-256
is `7f0ca8685b1d3c986ba25f3aa371b192e920a26a18be7270779e79814bd07601`
(279 lines). The original notice and mathematical statement are unchanged.
No compiler check at the same revision was repeated. The new exact-source
check is justified by actual diagnostics and the source change.

The pre-staging reader check omitted the then-untracked new module.
The compiler was started before the failed committed reader check was
inspected. That check rejected the exact `Public claim:` field of the
original-provenance notice. A subsequent complete comparison also found
the same notice fields in the four modules published in #8918. Thus the
earlier reported prose success was incomplete; the successful kernel
build and imported reports for #8918 are unaffected.

The proposed correction recognizes only an exact public-claim field
inside a complete original-provenance notice. Issue references in
mathematical comments and docstrings remain subject to the existing
reader rule. The narrow checker correction is independently approved. Its ten focused
regression tests passed in 0.041 s and are not repeated. The cleanup changes only three private simplification arguments. Prose,
statements, names, tags, imports and checker/test bytes are unchanged;
their successful checks remain applicable without repetition.
The narrow reader-checker correction is independently approved and its regression tests passed. The successful reader check remains applicable because the proof-only cleanup leaves prose and checker bytes unchanged. Approval record: /tmp/tnlean-8758-prose-metadata-review.json (SHA-256 b9c187ff55c112bb113fad14370db78affb4d4580ed963089a68fa8d8682be2d); regression log: /tmp/tnlean-8758-provenance-notice-prose-targeted-tests-1.log (SHA-256 b80a7392371a030e2d0652423de910a1543ee124a5bd8bd1561154408b0cd4cf). The checker and tests retain their exact corrected-source bytes. Mathematical issue references remain subject to the existing reader rule.

The retained temporary artifacts are not represented as committed
evidence:

| Temporary artifact | SHA-256 |
| --- | --- |
| `/tmp/tnlean-8758-actual-sector-assignment-first-canonical-failure.json` | `b10f83af6929794371249d3a100593cbd58d419d5d54d67881cf21620a2d3eab` |
| `/tmp/tnlean-8758-actual-sector-assignment-canonical-failed-1.log` | `96b11b0a3bf22f52402603ba53dc3a1e6c655f80b631dbb525aa74b2030e85cd` |
| `/tmp/tnlean-8758-actual-sector-assignment-build-failed-1.log` | `a0925be0dcdf9d384cd2f83a15c045ed593f4d9523e204e004a48bca2cc2f28d` |
| `/tmp/tnlean-8758-actual-sector-assignment-frozen-source-attempt-1.json` | `73db3eb08c8718b2c1860d36fbeb7b205bb4138cc368cf4f124e4f31ef582bf1` |
| `/tmp/tnlean-8758-actual-sector-assignment-reader-failed-1.log` | `8fa2999dc02fcf85407b1535bc2cc7c53d2031adcd7cba111ba7a980c7b81dbe` |
| `/tmp/tnlean-8758-actual-sector-assignment-source-binding-confirmation.json` | `7616fec773ee2975610369dc963df141c3c1efac334b32a0f7bbb8cd62308b56` |
| `/tmp/tnlean-8758-actual-sector-assignment-base-binding-confirmation.json` | `a4c88ba1695503aa64e61dc4aed47528ee09cb95c557e124701aa00342a14d96` |
| `/tmp/tnlean-8758-actual-sector-assignment-correction-application.json` | `bfd69030db27bf2b7af1416822d22603dec641222e20e3cfcd0f34fcfb46584f` |
| `/tmp/tnlean-8758-provenance-notice-prose-full-diff.log` | `d9c1b0e7a49db33b4206fe883dbdd977c9c02ab8cc83dde668ec8c0d9df7e7d8` |

### Warning-attempt temporary records

| Temporary artifact | SHA-256 |
| --- | --- |
| `/tmp/tnlean-8758-actual-sector-assignment-warning-attempt-2.json` | `07f06db2681e3fcb332f6153897e4b9a0be7584e57525974a8e4b0289bc22f4a` |
| `/tmp/tnlean-8758-actual-sector-assignment-build-warning-2.log` | `ae6a2739ce53e794f8e2b3598c56d25e1758435e5aae8a4ee57f14feab2a91bb` |
| `/tmp/tnlean-8758-actual-sector-assignment-axioms-warning-2.log` | `59a31a879abe02006cc1eb675242ec4227d5c603df379375a88b580b3d3fc007` |
| `/tmp/tnlean-8758-actual-sector-assignment-frozen-source-attempt-2.json` | `419e740904d01710f74f1c4d4ee8b9c649c86cfb021b79776a8c53f73f3e66c2` |
| `/tmp/tnlean-8758-actual-sector-assignment-canonical-corrected-2.log` | `6a8f40c2b73d727e93b2adafe341c9cb20de192fe478218cd48d915bcd5f605b` |
| `/tmp/tnlean-8758-actual-sector-assignment-source-supersession-2.json` | `29b768060d4b512784a732fea53691b32e1356a03fdbb286892d936773344ccc` |

The first strict promotion helper stopped with exit code 1 before any
output or production-shard write. Its two historical-freeze reads passed
strings to an API requiring paths. A separately reviewed helper correction
converts only those arguments to paths and retains the failure record
`/tmp/tnlean-8758-actual-sector-assignment-strict-helper-failure-1.json`
at SHA-256 `64d132990cddc3c08d37721735e8bfc2b7b1851d9b87e438bfaa0c4416a3f2c7`. No elapsed time was
measured for this helper failure, and no compiler check was repeated.

## Exact-source verification

| Check | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- |
| Canonical Geometry build | Passed, exit 0, no diagnostics | 18.827 s | 986fc3080faa601fa589a1911a82578b089693897dae32202473a045b383665c |
| Single imported kernel report | Passed, exit 0 | 4.676 s | fca2e146e8ad22608c3426192b6d1d5659b33336ea6a40010ee9bdb27f72f51c |

The imported report for the new theorem lists exactly propext, Classical.choice and Quot.sound. This is the sole successful canonical check at the corrected source. The earlier a5137f3071e1a7702b77071aaeae78aee9cafdae attempt failed after 18.269 seconds and produced no imported report. The next source c28d731278fd8c115ccf507f5dd9579e20046f81 passed its build in 31.849 seconds with three unusedSimpArgs diagnostics and its single standard-three imported report in 17.349 seconds. It was not promoted. The new source check follows removal of those three unused arguments. No direct check or old-record reverification is claimed.

The actual commands are `lake build TNLean.PEPS.AreaLaw.Geometry` and
`lake env lean docs/provenance/evidence/8758-actual-sector-assignment-axioms.lean`,
run serially under the repository lock in the sole warmed worktree.
Logs are `docs/provenance/evidence/8758-actual-sector-assignment-build.log`
and `docs/provenance/evidence/8758-actual-sector-assignment-axioms.log`.

Strict promotion and the unchanged normal policy passed all 316 records: one new original and all 315 unchanged parent records. Every parent shard and all measured recursive historical evidence files retain their exact bytes; no old row is reverified and no provenance policy, license or dependency pin changes. The separate reader-facing prose correction affects only the two guarded Python files.
The corrected strict helper passed in 35.993 s; the sole normal policy
command passed in 22.002 s, with exit code 0 and 316 valid entries.
The normal command was
`/Users/siruilu/.local/share/uv/tools/zotero-mcp-server/bin/python -B scripts/check_openai_provenance.py --root . --upstream-root /tmp/tnlean-openai-math-audit.git --repository-root LionSR/QICLean=.lake/packages/QICLean`.
Its retained temporary log is
`/tmp/tnlean-8758-actual-sector-assignment-normal-policy.log`, SHA-256
`6a1bf0efe8131bdee11a5283f7be78ed3035e196da854d114c42a8900983fc76`.
The corrected strict log is
`/tmp/tnlean-8758-actual-sector-assignment-strict-promotion-corrected-2.log`,
SHA-256 `8c214ed86540b7af8e78f0f9a1de88d46b9194abf270417d19089e15e2bc60f9`.
These temporary logs are distinguished from the two committed compiler logs.
No successful compiler or normal policy check was repeated.

Source synchronization passed total_blueprint_refs = 20264 and 20270 lines in blueprint/lean_decls, with complete reverse coverage.
2874 production modules and 75 generated import files.
Pinned formatting and idempotence, reader prose, module and source guards, independent mathematical review and scoped pattern review passed. The theorem derives nonempty Z and the lower fine exponent from the actual reference data; its only added public declaration is the actual sector assignment and exact closed local equality.
The changed-module timing assessment passed. No compiler check at the same revision was repeated; the new check follows actual diagnostics and a three-argument source cleanup.

The one scoped chapter contains one theorem, one proof and one declaration
tag. All five mathematical freeze files retain their source-revision bytes:

| File | SHA-256 |
| --- | --- |
| TNLean/PEPS/AreaLaw/Geometry.lean | `364d11a9939b4311b33e5955b94b01ae228e0d4ff304368a0a09b5fccf5b299f` |
| TNLean/PEPS/AreaLaw/Geometry/InitialSectorAssignment.lean | `ecf6843e119f52e6df2a6a75890d8010888e40164674be0a8e3fe141a6cd82a6` |
| blueprint/src/chapter/ch24_peps_area_law_actual_sector_assignment.tex | `aae87e7a44b53f12d00b0b82c45fed538709dc34ff8270d1f873072d14401eac` |
| blueprint/src/chapter/ch24_peps_regions.tex | `09d030a6855d5df0e2b27f8d2bad05aa00b860f3004f68ab36824a71d4eda10f` |
| docs/provenance/evidence/8758-actual-sector-assignment-axioms.lean | `9aed95542c0cb05ff42bd5d76a4f1bf16c7119847c408c6aded7a16902fe1567` |


All parent records, shards and all 164 recursively tracked historical
files remain unchanged. Raw strict promotion and the separately derived
single completion note remain distinct immutable artifacts. QICLean remains
pinned to `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

## Further obligations

Full CI and book rendering remain pending. The earlier local declaration
check was limited by the unrelated missing `TNLean/MPS/Examples/Fibonacci.olean`;
no successful full local declaration check is claimed here.

The assignment of the eight fixed sectors does not yet merge inactive rays
or establish the full active-ray assertion. Isolated stars, simultaneous
recursive repairs and the final finite lattice partition and estimates
remain further obligations. The full two-family proposition and both
headline PEPS/area-law theorems remain unproved by this contribution.
