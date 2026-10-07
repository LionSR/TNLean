# Colors of actual belt-cell fans

All four new declarations have passed exact-source canonical verification
and independent mathematical review. Every parent record and historical
evidence file remains unchanged. Full CI and compiled book checks are pending.

## Mathematical scope

Fix an arbitrary origin, finite endpoint set Z, width C ≥ 2, lower layer
k₀ ≥ 50,000,000 and arbitrary choices of the two belt residues at each layer.
An admissible reference is an actual belt cell at k ≥ k₀. Its fan uses the
actual split mask. No sparsity estimate or finite support of the residue
functions is assumed.

The color function takes values in Fin 2. A slot facing the dummy neighborhood
receives the opposite parity of k₀−1. A slot facing an actual nonbelt cell
receives the opposite parity of that cell's layer. Across two belt cells,
the nested lexicographic order of the layer and signed cell index assigns
an opposite pair of colors. The opposing identifier comes from the proved
unique-opponent choice; no label or opponent certificate is supplied.

Whole-segment containment in the dummy closure proves the displayed dummy
color and its inequality with the dummy parity. For an actual nonbelt cell
at h ≥ k₀ with a contact containing two distinct points, the nonbelt theorem
retains its actual pitch index J, contains the entire elementary segment in
that primary birth region and gives a color opposite to the primary parity.
The primary identifier is (h,J), including disconnected fragments. Cell
pair distinctness follows from belt versus nonbelt membership. No strict
inequality between fine and pitch scales is added.

For two distinct actual belt cells and arbitrary actual-mask slots whose
closed elementary segments share two distinct points, the two colors differ.
Reversed endpoints, matching-slot selection and uniqueness of a slot are not
assumptions. These are local coloring assertions. Global run and primary
labels, classification of all positive-length interfaces, isolated stars,
recursive repairs, descendants and both headline theorems remain further
obligations.

## Manuscript and independence

- Manuscript: OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11.
- Source revision: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- Manuscript path:
  `preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
- Label: `prop:two-families`; dummy parity at lines 172–174, primary
  parity at 212–218, and local fan coloring at 299–323.
- Original formalization from the manuscript mathematics; no upstream Lean
  source or proof text is reused. OpenAI Codex (GPT-6) assistance is disclosed
  separately from manuscript attribution.

## New declaration inventory

All four declarations are in `TNLean.PEPS.AreaLaw.Geometry`, in the new
`TNLean/PEPS/AreaLaw/Geometry/BeltFanColors.lean` module.

| Declaration | Kind | State |
| --- | --- | --- |
| `beltCellFanColor` | Noncomputable definition | Verified at the exact source below |
| `beltCellFanColor_dummy` | Theorem | Verified at the exact source below |
| `beltCellFanColor_nonbelt_opponent` | Theorem | Verified at the exact source below |
| `beltCellFanColor_belt_contact` | Theorem | Verified at the exact source below |

## Exact-source verification

Completed parent: `957de7bed210e037a8a082eae6ad5f9969565fb2`, draft [#8894](https://github.com/LionSR/TNLean/pull/8894).
Frozen source: `acff16af5c9f4726de4efbee7eb01f56729e42b1`.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Passed, exit 0 | 15.499 s | `bddacb00bfc0d33f7059b6338cafcefecff0e73cba9be8181103a835ad11e37c` |
| Imported four-name report | `lake env lean docs/provenance/evidence/8758-belt-fan-colors-axioms.lean` | Passed, exit 0 | 4.525 s | `8e1f475949bb2fd1bbeef26a67e2fb2e7aca6746fabeaf28453c7a99b8230529` |

Actual source, command headers, elapsed times, exit codes and complete output
are retained in [the build log](8758-belt-fan-colors-build.log) and
[the imported kernel log](8758-belt-fan-colors-axioms.log). Both commands
completed without diagnostics. All four reports satisfy the unchanged standard
logical-foundation policy. The exact five-file frozen manifest is preserved;
existing warm artifacts and the shared locked verification protocol were reused.

Strict promotion passes 279 records, adding exactly four original records.
All 275 parent entries and shards and all 120 tracked historical evidence
files are unchanged. No prior record is reverified. The separate unchanged normal provenance policy also passes all 279 records.

Full source synchronization passes with 20,233 distinct references and
20,227 flattened declaration records, with no missing, stale or duplicate
references and complete changed-declaration reverse coverage. Generated imports
cover 2,854 production modules in
75 files. The scoped chapter contains one
definition, three theorems, four declaration records and three proofs, with
seven completion markers. Pinned formatting is idempotent; reader-facing prose
and module guards pass. Independent full review approves the four exact
signatures and proofs. The author's direct package-option source check passed
without diagnostics in 14.91 seconds. The scoped pattern review is
recorded by the coordinating agent.

QICLean remains pinned to `8d5389d23c8e675a0117442e1a0d2c683a4bad41`; toolchain and dependency bytes
match the completed parent. Full CI and compiled book checks remain pending.
The historical local whole-library declaration check encountered the
pre-existing missing `TNLean/MPS/Examples/Fibonacci.olean`; its historical
evidence and limitation remain preserved. The narrow Geometry build does not
establish whole-book compiled verification.

## Immutable parent evidence

The completed parent contains 275 provenance records. This contribution
adds only four original records, for 279 in total. No parent proof module
or provenance record changed; no prior declaration was reverified. All parent ledger and record bytes must remain unchanged.

A new, separately named baseline captures every tracked file recursively
under `docs/provenance/evidence`: all notes, imported reports, logs and nested
evidence directories. The measured Git inventory contains 120 files. No
previous baseline was replaced. The strict helper guards every parent shard,
all 275 entry hashes, all 120 historical file hashes, the current policy,
schema, license, toolchain and dependency pins.

The strict helper checked the exact frozen source, original notices, four
reports and actual log hashes under the unchanged current policy. It ran
no compiler or cache operation and wrote only a new temporary promoted
shard. Every historical file and parent record remains retained.

## Separate integration ownership

Compression's next fixed-source contribution is published as
[#8893](https://github.com/LionSR/TNLean/pull/8893), source
`6246647741ce41a55a3897329336055330dd7e6f`, head
`4097a00b1ea14529fad15cb6d22d1b82c273e2db`.
Compression owns the TNLean integration; the analytic owner has the separate
QICLean integration. Geometry adopts neither integration nor a new pin.
The dependency remains `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.
