# Colors and regularity of actual initial regions

The two original records have passed exact-source canonical verification
and independent mathematical review.

The completed parent is draft [#8906](https://github.com/LionSR/TNLean/pull/8906),
evidence `aa2dea58b6945af6ca0d3a1c88b89ade7fbf0d03`, proof
`ff3ac34d661f011020c566dff01eed0fb6454881`. The root agent's complete immutable
capture measures 304 records across 26 ledgers and all 148 recursive tracked
historical evidence files. Every parent row, shard, historical file, policy,
license and dependency pin is retained unchanged. No old result is reverified.
The public parent handoffs are
[#8758, comment 6050300202](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6050300202)
and [#8733, comment 6050300360](https://github.com/LionSR/TNLean/issues/8733#issuecomment-6050300360).

## Mathematical statements

Fix an arbitrary origin, finite endpoint set, width C ≥ 2, initial layer
k₀ ≥ 50,000,000 and valid dependent residue choices. For distinct actual
initial identifiers, containment of an entire nondegenerate closed segment
in both birth regions forces opposite colors. This includes the dummy,
retained primaries and connected belt runs. Contacting primaries belong to
adjacent layers: locality bounds their indices, while separation excludes
distinct primaries in the same layer. Their parities therefore differ. A
primary contacting the dummy lies in the initial layer and has the opposite
parity. Actual run-interface results handle the other cases, with run colors
constant on constituent triangles. No regularity premise is used. Two isolated
common points of disconnected regions are not substituted for a shared segment.

Every actual initial birth region equals the closure of its open interior.
An actual triangle's nonzero determinant makes its edge vectors linearly
independent and its vertices affinely spanning. Convex-hull topology then
supplies nonempty interior and the closure identity. A contained unsplit fan
triangle supplies the same interior property for each closed dyadic square.
Finite unions of regular closed sets are regular closed: each constituent
interior lies in the union's interior, and closedness gives the reverse
inclusion after taking closures. Exact finite coarse-cell, nonbelt fine-cell
and fan-triangle decompositions apply this argument to dummy, primary and
run regions. The empty union and disconnected primaries are included.

Both statements allow an empty endpoint set, arbitrary real origin and
arbitrary valid residues. Neither assumes sparse shifts, finite support of
the entire ambient identifier family, a substitute geometric construction,
a contact certificate, or the desired regularity. These assertions concern
the actual initial construction before stars and recursive repairs.

## Manuscript and independence

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, pinned at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`, in
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
The interface theorem cites `prop:two-families`, lines 172–177, 212–218 and
299–323; its auxiliary arguments cite `geometry:nonadjacent`, lines 193–198,
`geometry:primary-pieces`, lines 246–249, and `geometry:layer-distance`,
lines 179–191. The regularity theorem cites `prop:two-families`, lines 154–177,
212–218 and 299–323, especially 308–316. It is an auxiliary property of the
actual initial regions, rather than the full two-family proposition.

Both statements and proofs are original; no upstream Lean source or proof
text is reused. OpenAI Codex (GPT-6) assistance is disclosed separately from
attribution. The public assignments are
[#8758, comment 6050110160](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6050110160)
and [#8758, comment 6050230173](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6050230173).

## Released source and independent review

| Module | Public inventory | Released SHA-256 | Direct wall / user / system |
| --- | --- | --- | --- |
| InitialRegionInterfaces.lean | One theorem | `9afa8cbd355e36c4c3091016598cd99fc7f65c4e1780e771f264011fe149c688` | 4.79 / 2.32 / 2.70 s |
| InitialRegionRegularity.lean | One theorem | `61e4dfe5bf66b6fe0a8a96d41f87de4eaf22180fc58dba55fad8805483dbd626` | 13.27 / 2.44 / 4.65 s |

Both complete package-option direct checks exited zero without diagnostics
and wrote no compiler artifacts. The successful interface log
`/tmp/tnlean-8758-initial-region-interfaces-direct-2.log` has SHA-256
`1050bf8e3ca2af62419d637367c7f9f8ea04e42df7788640d236df1d47c69681`.
The successful regularity log `/tmp/tnlean-8758-initial-regularity-direct-4.log`
has SHA-256
`a365a1eab7a29510487d915ec7d39ba2ca19d2cf2fdf4b9ba259150b413baaf2`.
The exact release manifests are
`/tmp/tnlean-8758-initial-region-interfaces-release.json` and
`/tmp/tnlean-8758-initial-region-regularity-release.md`. Prior failed checks
remain preserved there. Both final source hashes have complete independent
mathematical approval. Direct elaboration is not canonical verification,
and no successful full-file check is repeated without a new concern.

## Exact-source canonical verification

Frozen source: `eb7f6c0b9cb30358c0c5125aca3dba7ee56916ac`. Completed parent: draft
[#8906](https://github.com/LionSR/TNLean/pull/8906), evidence
`aa2dea58b6945af6ca0d3a1c88b89ade7fbf0d03`, proof `ff3ac34d661f011020c566dff01eed0fb6454881`.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Passed, exit 0 | 20.802 s | `ef2790841130c1b6a1c286f23fbd4ee48b717e5c3b805e8ece6493fb13380f9b` |
| Imported two-name report | `lake env lean docs/provenance/evidence/8758-initial-interfaces-regularity-axioms.lean` | Passed, exit 0 | 5.721 s | `e0223b964a5f1f8360789247c3dd8f1486a0857a0ec0da8f838aebea309b654f` |

Both raw logs retain exact revision, command, elapsed-time and exit-code
headers without diagnostics. The report prints exactly the two expected
names from two modules. The actual foundation sets are read from the
reports and must lie within the permitted standard foundations.
The measured sets are:

| Declaration | Actual axioms |
| --- | --- |
| `TNLean.PEPS.AreaLaw.Geometry.initialBirthRegion_eq_closure_initialOpenRegion` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.initialRegionColor_ne_of_segment_subset_inter` | Classical.choice, Quot.sound, propext |

Strict promotion, the unchanged normal policy and evidence finalization pass
all 306 records, adding exactly two originals. All 304 parent records and
shards and all 148 recursive historical evidence files remain unchanged.
No old declaration is reverified. The finalizer restores raw promotion to
the exact frozen planned rows and clarifies only the two new historical
preparation descriptions. Its derived output is byte-identical to the
normal-policy production shard. All seven Lean, audit and chapter byte
sequences remain frozen; policy, licenses, toolchain and dependency pins
are unchanged.

Source synchronization passes `total_blueprint_refs = 20254` and
20,260 lines in `blueprint/lean_decls`, complete reverse coverage and
no missing, stale or duplicate tags. Generated imports cover
2,866 modules in 75
files. The chapters contain two theorems, two proofs, two tags and four
completion markers. Independent review, formatting
idempotence, reader prose, module guards and pattern checks pass. The two
approved complete module direct checks retain their exact hashes and timings above.

Full CI and compiled book checking remain separate. The historical missing
`TNLean/MPS/Examples/Fibonacci.olean` limitation is preserved. QICLean remains
pinned to `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

## Further geometric obligations

The local sector and straight-ray descriptions, isolated stars, simultaneous
repairs, residual descendants and their quantitative bounds remain to be
proved. The finite lattice sampling and uniform summation estimates also
remain open. The two current assertions do not establish the full two-family
proposition or either headline PEPS/area-law theorem.
