# Initial region identifiers and the translated dyadic origin

The nine original records have passed exact-source canonical verification
and independent mathematical review.

The completed parent is draft [#8902](https://github.com/LionSR/TNLean/pull/8902),
evidence `aeae9a15b7d6a745676b04fda477e36e671e1cc2`, proof
`d5463154269cf320c7a176349b64589388220a0e`. Immutable capture measures all
289 records across 24 ledgers and all 140 recursive tracked historical evidence
files. Every parent row, shard, historical file, policy, license and dependency
pin remains unchanged. No old declaration is reverified. The parent handoffs
are [#8758, comment 6049867219](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6049867219)
and [#8733, comment 6049868433](https://github.com/LionSR/TNLean/issues/8733#issuecomment-6049868433).

## Mathematical statements

Fix an arbitrary origin, a finite endpoint set Z, width C ≥ 2 and initial
layer k₀ ≥ 50,000,000. At every layer choose arbitrary valid dependent residues.
The initial identifier family is the disjoint union of the dummy identifier,
the actually retained primary indices together with their layers, and the
actual belt-cell connected runs together with their layers and cells.
Distinct runs remain distinct identifiers even when their colors agree;
disconnected pieces of a primary retain their common pitch identifier.
No arbitrary substitute region, component representative, desired-property
field or coloring certificate is introduced. Global finiteness of this
identifier family is not asserted.

Each identifier determines its actual closed birth region: the dummy
closure, a retained primary birth region, or a belt-run region. Its initial
open region is the interior of that birth region. Its color is the dummy
parity k₀−1, primary layer parity, or the color descended through the actual
connected-component quotient. This descended color agrees with every
constituent triangle's color. The definitions allow Z to be empty.

When Z is nonempty, these closed birth regions cover the plane. A point in
the dummy neighborhood lies in its closure. Otherwise actual fine-cell
exhaustion supplies a cell above k₀ containing the point. Its closed square
is covered by actual runs when the cell is in the belt, and is contained in
its unique retained primary when the cell is outside the belt. This proves
closed coverage. It does not assert coverage of the plane or lattice by open
interiors, pairwise interior disjointness, or the full two-family partition.
The Z.Nonempty premise is explicit and appears in the source's exhaustion
argument at lines 169–170.

The prescribed dyadic origin is o=(√2,√3). Each coordinate lies in (1,2),
their sum lies in (3,4) and their difference in (−1,0). The strict rational
bounds 4/3<√2<2 and 5/3<√3<2, together with √2<√3, suffice. Hence none of
these four numbers is an integer. For every signed integer m, the four lines
x₁=o₁+m, x₂=o₂+m, x₁+x₂=o₁+o₂+m and x₁−x₂=o₁−o₂+m contain no integer
lattice point: one of these equations at an integer pair would express the
corresponding coordinate, sum or difference of o as an integer. This is
only the arithmetic prerequisite. Actual initial and repaired edge containment
in these supporting-line families remains a separate geometric assertion.

## Manuscript and independence

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, pinned at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`, in
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
The initial identifiers and accessors cite lines 172–177, 212–218 and 299–323;
the run-color accessor cites 313–318 and the closed cover additionally cites
154–177. The origin and four nonintegrality assertions cite 150–154;
the integer-translated line consequence cites 545–559. Each declaration's
notice records its exact narrower ranges. The two scoped modules do not mark
the full proposition, complete lattice partition or either headline theorem
as proved. All nine proofs and definitions are original; no upstream Lean
source or proof text is reused. OpenAI Codex (GPT-6) assistance is disclosed
separately from attribution.

The public assignments are
[#8758, comment 6049638844](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6049638844)
and [#8758, comment 6049666385](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6049666385).

## Released source and independent review

| Module | Public inventory | Released SHA-256 | Direct wall / user / system |
| --- | --- | --- | --- |
| InitialRegions.lean | Four definitions and two theorems | `63933f675dabbe34a0045fc763c40136df0c7378a9c1a9d839f4f0328207d88f` | 42.39 / 2.55 / 25.62 s |
| DyadicOrigin.lean | One definition and two theorems | `b39ce4624a3e9063fa56897d0648aaf0c08156529c0484289cd1827a4e2e00b9` | 9.44 / 2.14 / 5.05 s |

Both complete direct checks exited zero without diagnostics and wrote no
compiler artifacts. InitialRegions has 149 released lines; its release
manifest is `/tmp/tnlean-8758-initial-regions-release.md`. The direct log
`/tmp/tnlean-8758-initial-regions-direct-1.log` has SHA-256
`734aec7a815dd7994932ef4968bf6e62c9b8d80e10a512b9a3b0dca707eb69cf`.
DyadicOrigin has no separate release manifest; its exact raw source and
`/tmp/tnlean-8758-dyadic-origin-direct-1.log`, SHA-256
`36de6b41a0e8599fb3fca0eb09dbef3aa2531adc0242c571f1943e2cd14fe50b`,
are the single-check release evidence. Independent complete mathematical
reviews approve both released statements and arguments. No direct check is
treated as canonical verification.

## Exact-source canonical verification

Frozen source: `afb83051377658183c94673c0c2bd5a2f508a4d3`. Completed parent: draft
[#8902](https://github.com/LionSR/TNLean/pull/8902), evidence
`aeae9a15b7d6a745676b04fda477e36e671e1cc2`, proof `d5463154269cf320c7a176349b64589388220a0e`.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Passed, exit 0 | 14.208 s | `b3cda2e083a926119c33f59227ad52690641efb026389bfc3be3f57b1e881e1c` |
| Imported nine-name report | `lake env lean docs/provenance/evidence/8758-initial-regions-origin-axioms.lean` | Passed, exit 0 | 4.483 s | `e8b16b608d539c4ab2215be51dd7d455683aa1774242c057ffc6ae24cf00f39c` |

Both raw logs retain exact revision, command, elapsed-time and exit-code
headers without diagnostics. The report prints exactly the nine expected
names from two modules. Each actual foundation set is a subset of the permitted
standard foundations; no full three-element set is inferred for a definition.
The measured sets are:

| Declaration | Actual axioms |
| --- | --- |
| `TNLean.PEPS.AreaLaw.Geometry.InitialRegionIndex` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.dyadicOrigin` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.dyadicOrigin_nonintegral` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.dyadicOrigin_supporting_lines_avoid_lattice` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.initialBirthRegion` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.initialBirthRegions_cover` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.initialOpenRegion` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.initialRegionColor` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.initialRegionColor_beltRun_eq` | Classical.choice, Quot.sound, propext |

Strict promotion, the unchanged normal policy and evidence finalization pass
all 298 records, adding exactly nine originals. All 289 parent records and
shards and all 140 recursive historical evidence files remain unchanged.
No old declaration is reverified. The finalizer restores raw promotion to
the exact frozen planned rows and clarifies only the nine new historical
preparation descriptions. Its derived output is byte-identical to the
normal-policy production shard. All seven Lean, audit and chapter byte
sequences remain frozen; policy, licenses, toolchain and dependency pins
are unchanged.

Source synchronization passes `total_blueprint_refs = 20246` and
20,252 lines in `blueprint/lean_decls`, complete reverse coverage and
no missing, stale or duplicate tags. Generated imports cover
2,861 modules in 75
files. The chapters contain five definitions, four theorems, four proofs,
nine tags and thirteen completion markers. Independent review, formatting
idempotence, reader prose, module guards and pattern checks pass. Both
approved released direct checks retain their exact hashes and timings above.

Full CI and compiled book checking remain separate. The historical missing
`TNLean/MPS/Examples/Fibonacci.olean` limitation is preserved. QICLean remains
pinned to `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

## Further geometric obligations

Disjointness of initial open interiors, actual edge containment in the
four supporting-line families, coverage of lattice sites by the open
regions, global positive-length interface assembly, local sectors,
isolated stars and recursive repairs remain separate obligations.
Neither headline PEPS/area-law theorem is established.
