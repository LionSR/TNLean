# PEPS parent completion validation

Base: main `0e904435d645e416cd630cd2ac6646db6c74ef6e`.
Source: SCP10, arXiv:1001.3807v3, `Papers/1001.3807/paper_v3.tex`.
This record describes local validation before the draft PR's complete remote CI.
It does not report a full local aggregate Lake build.

## Mathematical review

- Native semi-regular parent classification derives the representation blocks,
  actual multiplicities, native orientation, and full parent-space dimension.
  Local invariance and seam movement prove membership of the actual commuting
  closures. Existing class independence and equal finite dimension give full
  kernel spanning. No closure expansion or kernel equivalence is a hypothesis.
- Physical G-isometric regional-parent commutation identifies the actual
  canonical projectors and handles rectangular site maps. Site-image support
  and the nonzero spectator factors used in cancellation are derived.
- The regular singleton-overlap intersection glues nonabelian flatness
  potentials under explicit overlap and no-cross-edge hypotheses. Localization
  removes exterior physical spectators. The concrete three-block range retains
  all eight virtual boundary legs and arbitrary correlated boundary inputs.
- Binary checkerboard blocking is a physical regrouping of the actual periodic
  bond contraction. It is not a physical disentangler or the general-group
  renormalization theorem.

Each component received an independent source/signature review and strict
elaboration. The stated restrictions are retained in the blueprint and audits.

## Lean checks

Lean is the repository's pinned 4.35.0-rc3 toolchain. QICLean dependencies were
checked against pin `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`.
Compatible artifacts were reused only after source/dependency provenance checks;
Mathlib was not rebuilt.

The combined initial proof audit covered 295 TNLean/QICLean dependency modules,
with 29 fresh private builds and nine central independent re-elaborations.
The native extension added 22 independently compiled modules in its dependency
closure; the regular-intersection review checked its three new modules and
140 dependency sources. These overlapping counts must not be added as a count
of distinct new modules.

Strict regressions use `autoImplicit=false`, `relaxedAutoImplicit=false`,
`pp.unicode.fun=true`, `maxSynthPendingDepth=3`, the standard Mathlib linters,
and `warningAsError=true`. Tests exercise rectangular physical maps, nonregular
multiplicity-two input, empty graphs, reversed edges, native periods three,
smallest positive binary coarse periods, and the nonabelian three-block model.
Guarded axiom checks allow only `propext`, `Classical.choice`, and `Quot.sound`.

A combined import probe checked all 579 declaration names in the new proof
fragments against compiled Lean environments. Complete source synchronization
resolved 18,635 references; reverse coverage found no missing blueprint entries
for changed public definitions, theorems, or lemmas.

## Blueprint and diagram checks

- General semi-regular transport: inspected 17-page focused PDF; browser tests
  passed four generated pages and 1,070 typeset expressions at 360/1440 pixels.
- Native classification: inspected 13-page focused PDF and source-wide reference
  checks. References to omitted prerequisites are expected in that isolated
  fixture and are checked again in the integrated source.
- Physical commutation and regular-intersection fragments were separately
  rendered and inspected.
- Five regular parent/intersection displays pass nine exact typed-panel boundary
  checks. Two native displays pass exact boundary/direction checks, including
  the eight-boundary/four-physical plaquette contraction.
- The complete event-stream sweep covers 487 pictures in 417 units with zero
  hard findings and 54 advisories. The current-main baseline has 473 pictures,
  408 units, zero hard findings and the same 54 advisories.
- The volume currently uses presentational equation displays, not hard
  `tenkzeq` equation scopes. Thus the sweep is not a proof of every displayed
  tensor identity; the focused signatures and Lean proofs are separate checks.
- All 209 referenced paper-gap slugs resolve. Formatting and generated-import
  checks are required before publication; full remote blueprint CI remains a
  separate gate.

## Remaining source scope

Native classification uses one unitary semi-regular representation and one
repeated site tensor, with both periods at least three. Link-dependent
representations, nonuniform native closure APIs, and smaller-period models
remain separate. The regular intersection does not yet cover arbitrary
semi-regular/G-injective sites. The literal four-cut source equality and
full general-group physical renormalization are separate ongoing targets.
No spectral-gap equality or local-unitary phase equivalence follows merely
from the linear parent-space equivalences proved here.
