# Disjoint initial interiors and unique regions at lattice points

The six original records have passed exact-source canonical verification
and independent mathematical review.

The completed parent is draft [#8904](https://github.com/LionSR/TNLean/pull/8904),
evidence `f93aec9cd0c6ae5dd399f44edd0d0d1e69d364e1`, proof
`afb83051377658183c94673c0c2bd5a2f508a4d3`. Complete immutable capture measures
298 records across 25 ledgers and all 144 recursive tracked historical evidence
files. Every parent row, shard, historical file, policy, license and dependency
pin is retained unchanged. No old declaration is reverified.

## Mathematical statements

For any translated dyadic square, optional midpoint subdivisions and assignment
of two colors, distinct connected runs have disjoint interiors. Distinct
constituent triangles meet only along a radial segment or at the center.
Each such intersection is nowhere dense in the plane, as is their finite
union. Thus the intersection of two distinct run regions has empty interior.
The colors may agree for distinct runs; connected components, rather than
colors alone, determine the run identifiers.

Fix an arbitrary origin, finite endpoint set Z, width C ≥ 2, initial layer
k₀ ≥ 50,000,000 and arbitrary valid dependent residues. The open regions of
distinct actual initial identifiers are pairwise disjoint. Half-open actual
fine cells are disjoint, and the interior of each square is dense in its
closure. These facts pass disjointness to the interiors of the relevant
closed-cell unions. The exact finite decomposition of each primary and the
actual cell containment of each belt run reduce the remaining cases to these
cell statements. The dummy interior is disjoint from later actual cells.
For runs in the same cell, the preceding nowhere-dense argument applies.
No nonempty endpoint set, sparse residue estimate, finite ambient family,
substitute region or desired disjointness certificate is assumed.

At the prescribed origin o=(√2,√3), the frontier of every actual initial
birth region avoids every integer lattice point. Dummy and primary frontiers
are contained in finite unions of actual square frontiers. For a fan triangle,
the finite closed fan cover puts a frontier point on the outer square frontier
or in an intersection with another triangle. The latter is a radial edge or
the common center. Actual marked vertices lie on the translated integer mesh,
and the allowed directions put these edges on one of the four supporting-line
families already proved to avoid integer lattice points. Run frontiers lie
in the finite union of their constituent triangle frontiers. Only frontier
inclusions are used: internal seams need not remain boundaries after a union.
The countable ambient identifier family is never treated as a finite union.

An initial open region is the interior of its birth region, so its frontier
is contained in the birth-region frontier. It also avoids the integer lattice.
Consequently an integer lattice point belongs to a birth region if and only
if it belongs to its open interior. These three assertions allow empty Z and
disconnected primary regions. They concern the actual initial construction
before stars and recursive repairs.

When Z is nonempty, the actual closed birth regions cover the plane. At an
integer lattice point this cover, the proved birth/interior equivalence and
pairwise disjoint interiors give exactly one actual initial open region.
The unique-region theorem uses the same C and k₀ bounds and arbitrary dependent
residues. Its nonempty endpoint-set premise is needed by the actual exhaustion
argument, which the source states explicitly at lines 169–170. The conclusion
is a partition of lattice points by the initial open regions, not a cover of
the entire plane by open interiors or a completed repaired partition.

## Manuscript and independence

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, pinned at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`, in
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
The generic run result cites lines 313–323. Pairwise initial disjointness cites
154–177, 212–218 and 299–323. The three lattice-frontier and membership results
cite 545–559 for the initial construction. Unique initial lattice membership
cites 154–177, 212–218, 299–323 and 545–559. Each declaration has its own exact
source notice. The full proposition, recursive repairs and both headline
PEPS/area-law theorems remain separate.

All six statements and proofs are original; no upstream Lean source or proof
text is reused. OpenAI Codex (GPT-6) assistance is disclosed separately from
attribution. The public assignments are
[#8758, comment 6049915425](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6049915425),
[#8758, comment 6049955038](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6049955038)
and [#8758, comment 6049997774](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6049997774).

## Released source and independent review

| Module | Public inventory | Released SHA-256 | Direct wall / user / system |
| --- | --- | --- | --- |
| InitialRegionInteriors.lean | Two theorems | `0300fc627381bfef6000e929c2d8f88cd17d69bd8a14fccaec44191774525b1b` | 15.08 / 3.11 / 7.08 s |
| InitialRegionBoundaries.lean | Three theorems | `ee5b1a83378275e96af04aaf38e87ac01941b97a8a2a9b937fd3e54484c27a7d` | 13.11 / 3.06 / 5.98 s |
| InitialLatticePartition.lean | One theorem | `44d3814a70dc1a32c2c2e5cf25a85c6077d1d472a52016a19fe4d6f7893665d2` | Not performed; first check is the canonical build |

Both supporting-module complete package-option direct checks exited zero
without diagnostics and wrote no compiler artifacts. Interiors direct log
`/tmp/tnlean-8758-initial-region-interiors-direct-3.log` has SHA-256
`2d674de480b3c187cf1e5428dce6dc838d134652a49094d1f4dfa84831d1e22d`.
Boundaries direct log `/tmp/tnlean-8758-initial-boundaries-direct-2.log` has SHA-256
`b2d58a5403033ecf59add37c4787bdecd21757163d7a1ebf3b63959cada7fc21`;
its precise release manifest is `/tmp/tnlean-8758-initial-boundaries-release.md`.
All three final sources have independent full mathematical approval, including
two independent complete reviews of the lattice consumer. That consumer has
no direct Lean check: its first check is the shared canonical build with the
actual compiled supporting modules. No direct check is treated as canonical
verification and no successful supporting check is repeated.

## Exact-source canonical verification

Frozen source: `ff3ac34d661f011020c566dff01eed0fb6454881`. Completed parent: draft
[#8904](https://github.com/LionSR/TNLean/pull/8904), evidence
`f93aec9cd0c6ae5dd399f44edd0d0d1e69d364e1`, proof `afb83051377658183c94673c0c2bd5a2f508a4d3`.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Passed, exit 0 | 19.578 s | `f492755e809a305beee9b39d6c043ce92d096b224bc90dd03ded542a2eb123fe` |
| Imported six-name report | `lake env lean docs/provenance/evidence/8758-initial-lattice-partition-axioms.lean` | Passed, exit 0 | 4.281 s | `ed3a9a8f5cd1de783e3394d0aed6d4ea96df71511587f8ad256d6c8b99dae5fa` |

Both raw logs retain exact revision, command, elapsed-time and exit-code
headers without diagnostics. The report prints exactly the six expected
names from three modules. The actual foundation sets are read from the
reports and must lie within the permitted standard foundations.
The measured sets are:

| Declaration | Actual axioms |
| --- | --- |
| `TNLean.PEPS.AreaLaw.Geometry.cellFanRunRegions_disjoint_interiors` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.exists_unique_initialOpenRegion_integerPoint` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.initialBirthRegion_frontier_avoid_lattice` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.initialBirthRegion_lattice_mem_iff_initialOpenRegion` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.initialOpenRegion_frontier_avoid_lattice` | Classical.choice, Quot.sound, propext |
| `TNLean.PEPS.AreaLaw.Geometry.initialOpenRegion_pairwise_disjoint` | Classical.choice, Quot.sound, propext |

Strict promotion, the unchanged normal policy and evidence finalization pass
all 304 records, adding exactly six originals. All 298 parent records and
shards and all 144 recursive historical evidence files remain unchanged.
No old declaration is reverified. The finalizer restores raw promotion to
the exact frozen planned rows and clarifies only the six new historical
preparation descriptions. Its derived output is byte-identical to the
normal-policy production shard. All nine Lean, audit and chapter byte
sequences remain frozen; policy, licenses, toolchain and dependency pins
are unchanged.

Source synchronization passes `total_blueprint_refs = 20252` and
20,258 lines in `blueprint/lean_decls`, complete reverse coverage and
no missing, stale or duplicate tags. Generated imports cover
2,864 modules in 75
files. The chapters contain six theorems, six proofs, six tags and twelve
completion markers. Independent review, formatting
idempotence, reader prose, module guards and pattern checks pass. The two
approved supporting-module direct checks retain their exact hashes and timings above.
The lattice consumer has no direct check: this canonical build is its first
Lean check, using the actual checked supporting modules.

Full CI and compiled book checking remain separate. The historical missing
`TNLean/MPS/Examples/Fibonacci.olean` limitation is preserved. QICLean remains
pinned to `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

## Further geometric obligations

Global positive-length interface assembly, local sectors, isolated stars,
recursive repairs, descendants and the required quantitative bounds remain
separate obligations. Neither headline theorem is established. The current
result concerns the initial ambient construction; lattice membership does
not assert an open cover of the plane or a completed full two-family partition.
