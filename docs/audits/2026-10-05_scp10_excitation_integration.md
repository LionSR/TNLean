# SCP10 flux paths and quantum-double local terms: integration audit

Date: 2026-10-05.
Integration base: `75c609dea22e633770ed1ea9609e985b282550a8`.

## Integrated packets

- Native dual-flux paths: `569e5e87b61607bb95aa1d49039b0be76feb0377`.
  Nine production modules, two regression modules, and three documentation
  files; 14 files and 2,774 added lines.
- Explicit quantum-double local terms:
  `88c42893c14581cdb54a54d3bf463c5ace2b7a08`.
  Four production modules, one regression module, three documentation files,
  and one diagram regression; nine files and 2,022 added lines.

Every file from both independently reviewed packets is retained byte-for-byte.
The integration regenerates the three PEPS import aggregators, routes each
blueprint fragment once into the existing chapter, and registers all three Lean
regressions and the quantum-double diagram regression in PR CI. The latter is
included in both workflow event filters and the blueprint-change job filter.
The existing blueprint-wide diagram sweep covers the flux display as well.
No existing mathematical Lean source, including the MPU-gauging development,
is changed.

## Verification

The final integrated sources were checked with Lean 4.35.0-rc3. All 13 new
production modules and three regression modules were freshly elaborated with
`autoImplicit=false`, `relaxedAutoImplicit=false`, `pp.unicode.fun=true`,
`maxSynthPendingDepth=3`, `linter.mathlibStandardSet=true`, and
`warningAsError=true`. All passed with empty diagnostics. Reused artifacts for
286 dependencies were matched to their reviewed hashes and their sources
compared against this integrated checkout or the exact QICLean pin
`2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`. No Mathlib rebuild was performed.

A combined-import harness checked all 163 named production declarations and
printed their transitive axioms. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. All 16 Lean files passed a comment-stripped forbidden-proof-
token scan. The three regression modules retain their nonabelian, inverse-class,
small-period, winding, nonzero-state, and actual-local-parent checks.

The generated-import check passes: 71 generated files cover 2,750 production
modules. Generator unit tests and blueprint scanner tests pass. The strict
source-based blueprint synchronization check resolves all 19,792 referenced
declarations, with no duplicate declaration ownership. Independent static
review confirms root import reachability without cycles, unique active chapter
routing, all 163 new declarations' blueprint ownership, and valid dependency
labels. YAML parsing and CI registration checks pass, as does `git diff --check`.

With Tenkz pinned at `08a6493f3605dcf2ca5b512823ccb2698dfc027b`, the
quantum-double regression passes its source/algebra checks, 70 declaration-name
checks, seven rejected mutations, three individual renders and combined render.
The flux fragment also renders successfully with the blueprint print preamble;
its two panels retain the same four directed virtual boundary legs and one
physical leg, with the prescribed rightward/downward native orientations.
External dependency lists are suppressed only in this standalone flux fixture;
their labels are checked against the complete blueprint separately. Both
focused render checks report no Tenkz audit findings or overfull boxes. The
rendered flux display, three quantum-double diagrams, and combined
quantum-double mathematical pages were inspected visually.

This is targeted integrated-packet validation. A full repository Lake build,
whole-book kernel `checkdecls`, complete blueprint PDF/web build, and remote CI
are not claimed by this audit. The registered CI checks retain those aggregate
gates. Publication and merging are separate actions.

## CI regression import correction

The initial private verification overlay emitted regression objects, whereas
PR CI originally ran the three files without writing objects.
`TorusDualFluxParent` imports fixtures from `TorusDualFluxString`, so CI failed
with an unknown `TNLeanTest` module prefix after the first regression passed.

The corrected step retains the same three files, ordering, strict options, and
three-minute timeout. It emits their objects into a fresh temporary
`TNLeanTest` directory on `LEAN_PATH`, then removes that directory on exit.
No test is added to the production library or persisted build cache, and no
production or regression Lean source is changed.

The original workflow commands reproduce the failure under actual `lake env`
with no `TNLeanTest` objects anywhere on the initial import path. The corrected
workflow commands pass twice from that same clean initial condition, with all
three regressions checked and no test objects left after either run.

## Mathematical boundaries retained

Flux deformation is proved for finite generated homotopies on positive-period
labelled tori. Measurement and local-parent conclusions require both periods
at least three; physical detection uses regular G-isometric tensors. The result
does not identify arbitrary same-endpoint or same-winding paths, equate winding
states with the vacuum, or establish the unrestricted open-boundary source
lemma. See `docs/paper-gaps/scp10_dual_flux_string_deformation.tex`.

The quantum-double packet proves the exact one-block image/kernel, coherent
normalized bond average, exact east–west two-block image, four-block-hole
flatness, and the specified ambient northern-bond commutation. The normalization
correction remains explicit. A full periodic common-kernel theorem, every
placed-term commutator, reverse four-block image, unrestricted topological-sector
classification, and unblocked T-to-K unitary transport remain open. See
`docs/paper-gaps/scp10_quantum_double_local_hamiltonian.tex`.
