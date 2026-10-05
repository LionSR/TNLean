# Exact mixed-endpoint MPO action

## Source and scope

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3, local source
`Papers/2203.12563/REsubmission.tex`:

- Lines 458–490 (`fusiontensors2`, `eq:orthoV`): exact action reconstruction
  and biorthogonal analysis/synthesis.
- Line 1269: exact local action is a source hypothesis for the MPS phase
  discussion, rather than a consequence of periodic covariance alone.
- Lines 1584–1598 (`defAgamma`): square-physical endpoint supports, retained
  diagonal tensors, cross-sector matrix units, and right bond weights.
- Lines 1600–1631: the mixed MPO with endpoint diagonal sectors and cross
  contractions of the action tensors.
- Lines 1632–1665 (`Agammasym`): exact local action along the interpolation.

`MixedEndpointMPO` constructs the mixed operator explicitly. The index
`Fin m` is shared by the two endpoint action decompositions; `m` is arbitrary.
The cross-sector entry in physical sector `(p,q)` is
`Σμ Wₚμ((α,k),r) Vqμ(s,(β,l))`. All unmatched physical or MPO-bond sectors
vanish. The enlarged maps retain only the matching acted sectors
`C₀ × B₀` and `C₁ × B₁`.

`MixedEndpointMPOWeights` proves transport of right bond multiplication
through the action tensor and commutation of the enlarged analysis with
the lifted bond weight. This gives the weighted identity without division.

`MixedEndpointMPOAction` reconstructs the unweighted letters by the four
physical sectors, then derives exact biorthogonal decomposition for the
actual `mixedEndpointInterpolation A₀ A₁ γ`. It also derives arbitrary-boundary
compatibility with a length-independent transport and the positive-length
periodic equation with eigenvalue `(m : ℂ)`.

There are no endpoint injectivity, fixed-point, nonzero-weight, spectral-gap,
or ambient-completeness assumptions. Every real `γ` is allowed, including
0 and 1. The periodic statement asserts an eigenvector equation, without
asserting nonvanishing of the state. Length zero is deliberately excluded:
the unmatched acted sectors prevent a general completeness identity.

## Deliberately separate obligations

This change does not construct mixed fusion maps or prove mixed MPO
closedness/injectivity. It does not align L-symbol gauges, identify F-data,
preserve physical adjoints, establish Hamiltonian commutation, or conclude
symmetric-phase equivalence. Those are distinct source obligations beyond
`Agammasym`. Endpoint exact action data are inputs; no property of the
constructed mixed action is assumed.

## Validation status

A strict combined-body Lean probe containing
all three production modules and the regression exited successfully with
no diagnostics on 2026-10-05. All three standard-axiom guards passed unchanged:
only `propext`, `Classical.choice`, and `Quot.sound` were reported.

This checks the actual declarations and proofs together against their external
imports; it is not a substitute for separately compiling the three importable
modules or running the repository build and full CI. The source-level integration checks below are historical; the subsequent
separate-module checkpoint is recorded at the end of this audit.

The source worktree itself performed no Lean invocation, cache mutation,
remote write, router/workflow edit, or checked blueprint marker. Textual
whitespace and proof-hole-pattern checks passed. The regression covers
arbitrary parameter and multiplicity, both endpoint specializations, the
periodic coefficient, and an explicit unmatched-sector obstruction to
ambient completeness.

## Local integration and pending checks

The local integration is directly stacked on commit
`8e4b8b718f92d901f5030b54135bd4c968f7bae7`, with tree
`d13923b1414266f4cbe156e70a347aaa30ee20a0`. This is the green PR #8691-equivalent base at
`dda8ab7388f89d20caf92c82b93bb3ff2cf69bc8`. The three production modules
and `TNLeanTest/MixedEndpointMPOAction.lean` are byte-for-byte equal to the
four-file source manifest of the final combined strict probe. Their complete
TNLean source-import closure is unchanged from the source worktree.

The generated `TNLean.MPS.Symmetry.MPOSymmetry` import list adds all three
modules. Chapter 30 includes the new action subsection immediately after the
mixed interpolation. The existing boundary-transport/action regression step
adds the Lean regression. PR CI and the main blueprint workflow run the native
mixed-action diagram test; their web jobs additionally run
`python3 scripts/test_tenkz_mixed_action.py --web-root blueprint/web --browser`
after installing Chromium. Trigger paths and the PR blueprint change filter
include the new Python script. Unrelated workflow steps and mathematical
content are preserved.

Local source-level verification passed:

- Import generation is current: 71 generated files cover 2,692 production
  modules; the sole changed aggregator adds exactly three imports.
- Blueprint declaration synchronization has no missing declarations. All 20
  new public declarations have exactly one blueprint owner, with zero checked
  statement or proof markers in the new leaf.
- The generator's nine unit tests and declaration-scanner regressions pass.
  The repository size check, new-file proof-integrity scan, Python syntax
  check, reader-facing prose check, and whitespace check pass.
- Both changed workflows parse as YAML, and each new browser command follows
  the existing Chromium installation in the same step.
- The native Tenkz regression passes both the actual print-wrapper and
  signature-audit modes with no hard findings. Its exact rational fixtures
  pass 3,780 coefficient checks at multiplicities 0, 1, 2, 3 and parameters
  -1, 0, 1/3, 1, 2. The unchanged focused generated web fixture has two equation
  wrappers and four pictures; the source lint has zero findings.

At the initial integration checkpoint, no separate Lean module, Lean
regression, aggregate import, repository build, full CI, or browser layout
check had run there. The new leaf's owners and proofs were then unchecked. The web result above inspects
the existing focused preview, not a newly built whole blueprint. The
fail-closed browser check remains for CI, including 1,440- and 360-pixel
viewports. No package installation, Lean cache mutation, or publication was
performed during integration. QICLean access for declaration synchronization
uses only a source-directory symlink at the exact pinned revision; no build
artifacts are copied.

## Separate-module checkpoint: 2026-10-05 22:58 UTC

All three production modules now pass the canonical targeted Lake build:
`MixedEndpointMPO`, `MixedEndpointMPOWeights`, and `MixedEndpointMPOAction`.
The standalone `TNLeanTest/MixedEndpointMPOAction.lean` also passes with
repository strict options and warning-as-error; all three guarded axiom
expectations match exactly. No source body changed from the earlier
combined probe. The new leaf therefore marks its six statement nodes and
four proof blocks checked, covering all twenty declaration owners.

Checked SHA-256 values:

- `MixedEndpointMPO`: `df5f91ba629e92c0fbbd80abce0abb4c09ebd9ddcd2b143441cf6e8ff1e33b35`
- `MixedEndpointMPOWeights`: `ba89ff855bb3f31f52266a2978fcdcde7700d54d729a076cc8e714b9c90f5142`
- `MixedEndpointMPOAction`: `c6ee97cace5ce047cb96d193bcaeb3c38966fd290f35ba7c5306cd66e1078c8d`
- Regression: `4d147f0f04d61049d5652839a9c85adeceda66e5169104f2253cd1b05d7d2dc5`

Full exact-head CI, integrated whole-blueprint rendering and browser layout
remain pending; the earlier focused rendering is not a substitute for them.

The checked-marker version was also rerendered as a nine-page focused PDF.
The three affected mathematical pages were visually inspected: diagrams,
indices and contractions remain legible, with no overflow or unresolved
references. One benign underfull-paragraph warning remains; full integrated
web/browser checks are still reserved for CI. Independent source review found
no mathematical, scope, diagram-semantic or CI-gate blocker.
