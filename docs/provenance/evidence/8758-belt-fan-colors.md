# Colors of actual belt-cell fans

The complete module and all four unchanged public signatures have passed
the direct package-option Lean check and independent mathematical review.
The four original records remain planned until exact-source canonical verification.

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

## Proposed inventory

All four declarations are in `TNLean.PEPS.AreaLaw.Geometry`, in the new
`TNLean/PEPS/AreaLaw/Geometry/BeltFanColors.lean` module.

| Declaration | Kind | State |
| --- | --- | --- |
| `beltCellFanColor` | Noncomputable definition | Released and reviewed; canonical verification pending |
| `beltCellFanColor_dummy` | Theorem | Released and reviewed; canonical verification pending |
| `beltCellFanColor_nonbelt_opponent` | Theorem | Released and reviewed; canonical verification pending |
| `beltCellFanColor_belt_contact` | Theorem | Released and reviewed; canonical verification pending |

## Verification

Completed parent: `957de7bed210e037a8a082eae6ad5f9969565fb2`, draft
[#8894](https://github.com/LionSR/TNLean/pull/8894), with verified reciprocal
source `b8c1e59e88eadf8694530d1a6fc470d8348c237e`.
Frozen color source: **unbound**.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Pending | Pending | Pending |
| Imported four-name report | `lake env lean docs/provenance/evidence/8758-belt-fan-colors-axioms.lean` | Pending | Pending | Pending |

The author's complete package-option check passed without diagnostics in
14.91 seconds (user 2.49 seconds, system 7.22 seconds). Independent full
mathematical review approves all four signatures and proofs. The canonical
build and imported reports remain pending. Source synchronization and reverse
coverage pass; imports cover 2,854 modules in 75 files. The scoped chapter
contains one definition, three theorems, four declaration records and three
proofs. Full CI and compiled whole-book checks remain pending.

The historical local whole-library declaration check limitation from the
pre-existing missing `TNLean/MPS/Examples/Fibonacci.olean` remains preserved.
Current #8876 book checks are running and compile-time checks are queued;
#8888 Lean and book checks pass while compile-time checks are queued; #8892
checks remain queued. These parent statuses do not verify this new source.

## Immutable parent evidence

The completed parent contains 275 provenance records. This contribution
adds only four original records, for 279 in total. No parent proof module
or provenance record is expected to change; no prior declaration is planned
for reverification. All parent ledger and record bytes must remain unchanged.

A new, separately named baseline captures every tracked file recursively
under `docs/provenance/evidence`: all notes, imported reports, logs and nested
evidence directories. The measured Git inventory contains 120 files. No
previous baseline was replaced. The strict helper guards every parent shard,
all 275 entry hashes, all 120 historical file hashes, the current policy,
schema, license, toolchain and dependency pins.

Promotion is disabled until the helper is bound to an exact frozen source
and successful actual build and four-name imported logs are available. The
helper checks committed source, notice, shard and imported-report inventory,
actual log headers and hashes, the standard logical-foundation policy and
the unchanged normal policy over all 279 records. It performs no compiler
or cache operation and writes only a new explicit output beneath `/tmp`.

## Separate integration ownership

Compression's next fixed-source contribution is published as
[#8893](https://github.com/LionSR/TNLean/pull/8893), source
`6246647741ce41a55a3897329336055330dd7e6f`, head
`4097a00b1ea14529fad15cb6d22d1b82c273e2db`.
Compression owns the TNLean integration; the analytic owner has the separate
QICLean integration. Geometry adopts neither integration nor a new pin.
The dependency remains `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.
