# Bounded-width strip entropy and MPS approximation

Issue: [TNLean #9552](https://github.com/LionSR/TNLean/issues/9552).
Original proof base: `825848d3832793c5d0622536f53e492cac9092b0`.
Publication base: `7137c7c7452f91c21ebdd7283536fe09939fd62f`.

## Mathematical boundary

The physical domain is the literal lattice rectangle `[0,L) × [0,w)`, with an
explicit equivalence to `Fin L × Fin w`. The Hamiltonian is
`TNLean.Lattice.LocalHamiltonian`, with one term per distinct nonempty
admissible support. It is not a column-blocked model of dimension `q^w`.

The public theorems `TNLean.MPS.AreaLaw.stripAreaLaw` and
`TNLean.MPS.AreaLaw.stripMPSApproximation` quantify their constants before
`L,w,J,Δ,H,E₀,Ω`. They assume `L,w,q ≥ 1`, `J ≥ 0`, `Δ > 0`, and precisely
`Matrix.IsGappedGroundState H E₀ Ω Δ`: a unit eigenvector and
`H - E₀ I ≥ Δ (I - |Ω><Ω|)`. This is the unique-ground-vector convention of
the one-dimensional note's preamble (lines 193–206). A merely gapped
degenerate ground space is not asserted to suffice.

The conclusions are column-interval entropy at most
`C₀(q,R) (1+J/Δ) w²`, and a normalized MPS on all `L*w` physical `q`-level
sites in an explicitly alternating column-snake ordering, with physical-space
error at most `1/L` and bond at most
`exp(C(q,R) (1+J/Δ) w²) * L^(c(q,R) sqrt(1+J/Δ) w)`.
`exists_stripMPS_norm_sub_le` returns the normalized approximant in the original
lattice Hilbert space. There is no entropy, tail, cutwidth, or filtered-energy
hypothesis. No positive-logarithm or asymptotic-size threshold excludes `L=1`.
Range zero, dimension one, clipped intervals, and partial columns are covered.

## Provenance and correction

These are strip extensions proposed by issue #9552, not statements reproduced
verbatim from the source note. The proof follows
`docs/notes/one_dimensional_note/part1_arealaw.tex`, counting at lines 29–53,
tails at lines 152–166, Lemma `lem:buffer` at lines 405ff, the closure at
lines 648–679, and Remark `rem:sharper` at lines 702–748.

The issue's bound `q^(R+1)` is false for lattice supports: a diameter-two cross
has five sites. We reuse the public lattice bounds
`v_R = 1 + 2R(R+1)` and `μ_R = 2^(2R(R+1))`, obtaining support dimension
`q^v_R`, independent of width. Every interval-crossing support has an inside
anchor in at most `2Rw` sites, so `N_R = 2R μ_R`. Every partial-column prefix
has at most `(R+1) μ_R w` crossing supports.

With `ℓ = log(e q^v_R)`, `b = 1 + N_R ℓ²`, `t = 1+J/Δ`, choose
`m = ceil(4 + 64e(J/Δ) b w + 128 sqrt(t b w))`.
The actual weighted interaction-energy sum is derived to be at most
`32e J b w / m ≤ Δ/2`. The true buffer has at most `2mRw` sites.
Writing `M = 5 + (64e+128)b`, the closure gives
`C₀ = (8R log q + log 2) M + 1024e b`.

For prefixes put `b' = 1 + (R+1) μ_R ℓ²` and
`A = sqrt(2 exp(e/2))`. The MPS constants are
`c = 128 sqrt(b')` and
`C = C₀ + log q + 64 sqrt(b') (log(2A)+1)`.
Sequential truncation uses `L*w` sites and accuracy `1/L`; its slack is
`64 sqrt(t b' w) log(2L²wA)`. Its unnormalized error is at most `1/(2L)`;
normalization at most doubles it. The width logarithm is absorbed into the
exponential width factor using `sqrt(w) ≤ w`, `log(w) ≤ w`, and `sqrt(t) ≤ t`.

## Source ownership and independent review

The three owned proof modules are:

- `TNLean/MPS/AreaLaw/StripGeometry.lean` (258 lines).
- `TNLean/MPS/AreaLaw/StripBufferDiscount.lean` (333 lines).
- `TNLean/MPS/AreaLaw/StripApproximation.lean` (504 lines).

Integration updates are the generated area-law aggregator, the strip section
of `ch35_one_dimensional_chain.tex`, its two role-registry entries, and the
tactic-pattern candidate for the privately packaged normalization argument.
No existing proof module or `SnakeGrid*.lean` file was edited.

An independent native source review inspected the
source note, pinned QIC APIs, actual proof bodies, final exported statements,
and final Blueprint formulas. Its final review passed the hypotheses,
constant order, corrected support counts, energy derivation, normalization,
site relabeling, all-prefix bounds, and all requested edge cases. It did not
independently rerun Lean or repository checks.

## Validation performed

- Preserved Lean `v4.35.0-rc3`, Mathlib commit
  `c55e6e786f49471c72fbddbec5415808896aec1e`, and QICLean pin
  `acda92aa70e69b37507e422bceb5414036859fe6`. Dependency source checkouts
  remained clean. Toolchain, Lake configuration, and manifest have no diff.
- Before builds, `lake exe cache get` with a writable cache directory
  recognized all 8,943 decompressed prebuilt cache files, with no downloads;
  the matching `Mathlib.olean` was verified. No Mathlib Lean-source rebuild
  was performed. The text-style executable compiled its native dependencies.
- Targeted Lake builds of all three modules passed. Final module build times
  were approximately 3.4s, 15s, and 13s respectively.
- All three sources passed the CI strict flags, including
  `autoImplicit=false`, `relaxedAutoImplicit=false`, the Mathlib standard
  linter set, and `warningAsError=true`; all three strict logs were empty.
- Temporary native checks resolved all 48 public declaration names.
- Five temporary boundary regressions passed: range-zero crossing count,
  clipped/empty buffer cardinality, and complete actual-name MPS theorem
  specializations at `R=0`, `q=1`, and `L=1`.
- Eight transitive axiom checks, including both uniform conclusions and
  `exists_stripMPS_norm_sub_le`, reported exactly `propext`,
  `Classical.choice`, and `Quot.sound`. The temporary `#print`/`#check`
  commands were not added to production or committed as test fixtures.
- Generated import aggregators are current. The TNLean import closure from
  the three modules is acyclic (44 reachable modules).
- Blueprint/source synchronization and reverse coverage of the new public
  declarations passed. Native declaration checks cover every new Blueprint
  reference. The changed chapter's role assignments and references passed.
- All 19 applicable Python tests for import generation, Blueprint roles,
  and Blueprint/source synchronization passed.
- Repository text-style lint, proof-integrity source scan, tactic-pattern
  scan, module-size checks, and `git diff --check` passed.

Publication preflight on the publication base repeated the targeted build, all
three strict checks, 48 native declaration checks, five boundary regressions,
eight transitive axiom audits, generated imports, and the 19 Python tests; all
passed. The ignored Blueprint declaration index was regenerated for the new
main snapshot, after which source synchronization and reverse strip coverage
passed. Independent integration review confirmed unchanged proof bytes and
preservation of all current-main tactic-ledger entries.

The global Blueprint role checker reports four failures in the untouched
`ch35_aklv_energy_truncation.tex`: theorem/lemma roles at lines 32, 85, and
366, and a reference word at line 90. Checking an archived `origin/main`
copy produced byte-for-byte identical diagnostics. The strip changes do not
add a role failure. These unrelated failures were left unchanged.

Not run locally: the full TNLean library build, whole-root `lake exe checkdecls`,
or Blueprint web/PDF rendering. Hosted CI remains a separate validation gate.
There is no remaining mathematical blocker for the scoped strip result.
