# Fan frontiers and geometry near an actual fine-cell mark

Canonical source verification has passed without diagnostics.

The exact source revision is `8f86fd6d2e20a77f6c130274cbaad6c5b9f3a60e`. The completed parent is draft
[#8907](https://github.com/LionSR/TNLean/pull/8907), evidence
`74d88251d951ced6bdb4b9fdbc251c84e20b5aaf`, with proof `eb7f6c0b9cb30358c0c5125aca3dba7ee56916ac`.
Its immutable capture contains 306 records across 27 ledgers and all
152 recursively tracked files beneath `docs/provenance/evidence`.
Only three boundary records may receive an appended history note and fresh
verification. The other 303 records and every unaffected ledger remain
unchanged. Every historical file, policy, license and dependency pin is retained.

## Mathematical statements

For an arbitrary real origin, natural dyadic exponent, signed cell index and
midpoint mask, the frontier of each actual fan triangle is contained in the
frontier of its square together with the actual radial segments from the
center to the fan endpoints. The finite closed-cover and closed-triangle
arguments are moved unchanged from the boundary module into the shared fan
module. The existing boundary argument uses this inclusion; its three public
statements and proof bodies are unchanged. An unused private mesh-point
argument is removed.

Let the width satisfy C ≥ 2, and let the reference layer satisfy
k ≥ 50,000,000. If an actual fine cell from layer h meets the closed ball of
radius 10t around an actual reference-cell mark, where
t = 2^(fineScaleIndex k), then h ≤ k + 1 and k ≤ h + 1. The two fine
exponents differ by at most one, and the marks of both cells lie on the
reference mesh with spacing t/4. The sixteen-side separation of nonadjacent
layers proves the assertion for a closed ball, including its boundary.
No separate late bound on h, selected belt membership or distinct-cell
premise is required.

For C ≥ 2, k ≥ 50,000,000 and k₀ + 1 ≤ k, every point of the closed initial
dummy neighborhood is at distance at least 16 · 2^(fineScaleIndex k) from
every point of the closed later layer. The endpoint witness is obtained
from actual dummy membership. No nonempty-endpoint hypothesis or late bound
on k₀ is added. Both near-mark results allow arbitrary origins and endpoint
sets. All three results concern the actual initial construction.

## Manuscript and independence

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, pinned at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`, in
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
The frontier inclusion cites `prop:two-families`, lines 299–323, and
`geometry:initial-stars`, lines 333–370, especially 352–359. The near-mark
mesh result cites `geometry:initial-stars`, lines 352–359. The dummy
separation also uses `geometry:layer-distance`, lines 179–191, and the scale
comparison at lines 200–207.

The manuscript describes the grids as “common translated”; the formal
conclusion retains the actual shared origin and quarter-mesh spacing.
[Pinned manuscript, lines 299–306](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L299-L306).
The new proofs are original, with no upstream Lean source or proof text
reused. The relocated arguments were already part of TNLean. OpenAI Codex
(GPT-6) assistance is disclosed separately from attribution; submission and
human review responsibility remain with the maintainer.

The public assignments are
[#8758, comment 6050315669](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6050315669)
and [#8758, comment 6050341951](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6050341951).

## Released source and independent review

| Module | Released SHA-256 | Direct wall / user / system |
| --- | --- | --- |
| FanFrontiers.lean | `cb2ee8c85f1b723bf3b3626bdb664c024e68c0b75887b44056577d7f2aadc5e8` | 11.46 / 2.03 / 5.55 s |
| NearMarkGeometry.lean | `7f4216ff37864c5050c9638770b00c9e52e2f631c1b2f3bdead3aefcc4352268` | 4.59 / 2.10 / 2.73 s |
| Reused InitialRegionBoundaries.lean | `92189759852c9458cfc01ecd47a6b0a00684607bfed9cc55f937e6c9c1bdae47` | No direct repeat; the canonical build is its first check at this source |

Both new modules passed full package-option direct elaboration without
diagnostics and without writing compiler artifacts. Independent mathematical
review approved the exact final signatures and proofs, including the reused
boundary argument and removal of the unused helper.

The successful direct logs are
`/tmp/tnlean-8758-fan-frontiers-direct-1.log`, SHA-256
`31347af4dc0aa7db77babc3cc171171de2df4bcc4c6d2dfaf02dfdc53ce02da6`, and
`/tmp/tnlean-8758-near-mark-geometry-direct-2.log`, SHA-256
`3641f909fdd8eacd2ad199efd862c6a1e850789b92e44a9628faadc4a3dc1359`.
The first near-mark diagnostic is preserved in
`/tmp/tnlean-8758-near-mark-geometry-direct-1.log`, SHA-256
`1d5d4f21cf5299d8d4750083ed5e5aa7a4ae5078349942bb371c64a2843232e4`.
Its sole correction made an existing real-power inequality's type explicit;
neither mathematical statement changed. The release records are
`/tmp/tnlean-8758-fan-frontiers-release.json` and
`/tmp/tnlean-8758-near-mark-geometry-release.md`.

## Exact-source verification

| Check | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- |
| Canonical Geometry build | Passed, exit 0, no diagnostics | 24.979 s | 15271144e2e29df8a68e206fa4ae636d07811192494096e8521584d42785caf0 |
| Six imported kernel reports | Passed, exit 0 | 5.261 s | e822ff566228c1cc9f57cff10b972a16991b5ea51aa5f6943621ec9a0789e105 |

All six exact quoted reports use only propext, Classical.choice and Quot.sound, or a subset of these foundations. The three reused boundary conclusions receive fresh source-bound evidence; their statements and public proof bodies are unchanged.

The commands are `lake build TNLean.PEPS.AreaLaw.Geometry` and
`lake env lean docs/provenance/evidence/8758-fan-frontiers-near-mark-axioms.lean`,
run serially in the existing warmed worktree under the repository lock.
The actual logs are `docs/provenance/evidence/8758-fan-frontiers-near-mark-build.log`
and `docs/provenance/evidence/8758-fan-frontiers-near-mark-axioms.log`.

Strict promotion and the unchanged normal policy passed all 309 records: three new originals, three boundary reverifications and 303 immutable parent records. All 152 recursively tracked historical evidence files are byte-identical; no policy, license or dependency pin was changed.

Source synchronization passed total_blueprint_refs = 20257 and 20263 lines in blueprint/lean_decls, with complete reverse coverage.
2868 production modules and 75 generated import files.
Pinned formatting and idempotence, reader prose, module and source guards, independent mathematical review and the scoped pattern review passed. The ledger records reuse of the existing public mesh inclusion and Mathlib singleton normalization; no additional public result is introduced.
The changed-module timing assessment passed without repeating a successful compiler check.
The two scoped chapters contain three theorem statements, three proofs and
three declaration tags. QICLean remains pinned to
`8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

The eight frozen files retain their exact source-revision bytes:

| File | SHA-256 |
| --- | --- |
| TNLean/PEPS/AreaLaw/Geometry.lean | `68a759333929f8c9fe1bd63cfa496b1c5dc2112ab24a0b2d211d088601f15fa2` |
| TNLean/PEPS/AreaLaw/Geometry/FanFrontiers.lean | `2acfdfa8fd5d9403d77e8d250610636c28d5fcb8c35f09718a82340f511ded22` |
| TNLean/PEPS/AreaLaw/Geometry/InitialRegionBoundaries.lean | `8bb445c9c7add114a7dc61ee3b8f2a4ff6069a7d988ff5b5119119788cd80c16` |
| TNLean/PEPS/AreaLaw/Geometry/NearMarkGeometry.lean | `afa4956f23b0dcc2da1af73db75591664a048dfdf61537a16bf35606c94ef46c` |
| blueprint/src/chapter/ch24_peps_area_law_fan_frontiers.tex | `928124edb634d7ac9ae5e12a63eccf3980604194de35f6bc376c7b8fa916907a` |
| blueprint/src/chapter/ch24_peps_area_law_near_mark_geometry.tex | `61cc92bddc9f5e148a5405a49a2ef83fb9c0bc004ae12a996f8c650b61bec069` |
| blueprint/src/chapter/ch24_peps_regions.tex | `55cc027ef96c5f607479605e6093c35245a3b83d2be569753898f286dfd68380` |
| docs/provenance/evidence/8758-fan-frontiers-near-mark-axioms.lean | `85374425d54e7874c9b03b9ee545a0043a97ee1414239e17d7782fde7e81c8f3` |


## Retained prior evidence

The containing boundary module changed, so the exact-current-file rule
requires fresh evidence for its three public conclusions. Each affected row
retains its identity, source references, license, notices and original history.
Only its verification record is replaced, with a history note identifying
the original evidence. The completed parent retains all earlier ledger bytes;
all 152 historical files remain byte-identical in the new tree.

| Declaration | Original source | Retained original logs |
| --- | --- | --- |
| TNLean.PEPS.AreaLaw.Geometry.initialBirthRegion_frontier_avoid_lattice | ff3ac34d661f011020c566dff01eed0fb6454881 | docs/provenance/evidence/8758-initial-lattice-partition-build.log, docs/provenance/evidence/8758-initial-lattice-partition-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.initialBirthRegion_lattice_mem_iff_initialOpenRegion | ff3ac34d661f011020c566dff01eed0fb6454881 | docs/provenance/evidence/8758-initial-lattice-partition-build.log, docs/provenance/evidence/8758-initial-lattice-partition-axioms.log |
| TNLean.PEPS.AreaLaw.Geometry.initialOpenRegion_frontier_avoid_lattice | ff3ac34d661f011020c566dff01eed0fb6454881 | docs/provenance/evidence/8758-initial-lattice-partition-build.log, docs/provenance/evidence/8758-initial-lattice-partition-axioms.log |


## Remaining obligations

Full CI and book rendering remain pending for this contribution. The earlier
local declaration check was limited by the unrelated missing
`TNLean/MPS/Examples/Fibonacci.olean`; no completed full local declaration
check is claimed here.

Active rays, sector assignment, isolated stars, simultaneous repairs,
residual descendants and their quantitative bounds remain further obligations.
The finite lattice sampling and uniform summation estimates also remain open.
These three auxiliary results do not establish the full two-family proposition
or either headline PEPS/area-law theorem.

## Preparation of the evidence

The first strict promotion attempt stopped before writing output because macOS
resolves `/tmp` to `/private/tmp`, while the temporary helper compared the
resolved output with the unresolved prefix. Exactly four path comparisons in
three temporary helpers were corrected to use the resolved prefix. Independent
review confirmed the precise change and unchanged BASE, SOURCE, source files,
policy and completed compiler logs. The failed invocation is retained at
`/tmp/tnlean-8758-fan-frontiers-near-mark-strict.log`, SHA-256
`1ebe25f6560bf783e489da5dca3e6b5af9beb5dcdb49cdecaa1cec38b9b0612c`.
The corrected failed step then passed; the unchanged normal policy ran once.
No successful compilation or normal-policy check was repeated.
