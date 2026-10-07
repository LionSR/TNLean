# Local evidence for the one-hole encoder

This packet records local checks of author checkpoint
`4fa931f810ac576e0142fa955af5fcbd71b2615a`. The production module is byte-identical
to its checked `9df423084befda1874fcf9f7eba289e70d529aaf` version. Evidence was
assembled from existing runs; no Lean build was run while preparing this
packet.

## Successful checks

[`verification.json`](verification.json) selects the successful rows from the
original [run records](runs), records the exact command strings and process
exit codes, and binds them to current source hashes and normalized log hashes:

- [Strict source elaboration](source-strict.log), with both implicit-variable
  options disabled, Mathlib standard linters enabled, and warnings as errors.
- [Thirteen consumer examples](consumers-strict.log).
- [Twenty-two axiom guards](guards-strict.log), checked against their expected
  reports in `TNLeanTest/HoleEncoderAxioms.lean`.
- [Twenty-two unguarded reports](public-axioms.raw.log), produced by the
  unchanged [`HoleEncoderAxioms.lean`](HoleEncoderAxioms.lean) driver.

Every public declaration has exactly the reported axiom set
`[propext, Classical.choice, Quot.sound]`. The ledger, production declarations,
guards, raw driver, raw output and rendered declaration links cover the same
twenty-two names. The source, consumer, guard and raw-driver SHA256 values
match the inspected checkpoint. These are individual `lake env lean` checks,
not a full-root build.

The [native build log](native-build.log) also reports success. It is supporting
log-only evidence: its top-level invocation and process exit code were not
captured, so neither is reconstructed or used as a ledger command.

## Superseded runs

The [history directory](history) preserves the first production failure and
repairs 1–7, plus the first consumer/driver failures and the consumer repair
with a missing `end`. Repair 7 built with warnings; it is not presented as a
clean strict pass. Native historical logs do not record process exit codes or
source hashes. The three failed strict runs have recorded exit code 1 and
their original source hashes in the retained run records. Historical
diagnostics, including elaboration-generated proof holes, are not current
source or axiom-audit results.

## Focused rendering

The [final report](render/final-verification.json) records successful local
PDF and static HTML generation, twenty-two declaration links for the new
leaf, all seven of its equation anchors, inspection of all eight PDF pages
and both diagram rasters, and two unchanged passes of pinned latexindent
3.24.7. The supporting [automated checks](render/automated-verification.json),
[source manifest](render/focus-manifest.json),
[format check](render/format-verification.json) and
[static-source check](render/static-source-check.json) are retained.

The exact inherited #8809 nested-cylinder leaf at
`c8a2fdfc19895245cc71f6f6c0fdff8f5da32592` still has six missing static equation
anchors, affecting eight reference links. Its PDF labels resolve. These
inherited gaps are separate from the new leaf's clean anchor checks; their
names remain explicit in both reports and the verification index. Renderer
warnings and the inherited empty bibliography page are also retained in the
reports.

Generated PDF, HTML, SVG and raster assets are not committed. Their recorded
hashes identify the inspected local outputs. Rendering build logs and the
full environment-input inventory are also omitted from this compact packet;
their hashes remain in the reports. No live-browser/MathJax execution,
full-book build or remote declaration availability is claimed.

## Normalization and limits

`verification.json` maps every retained original artifact's SHA256 to its
normalized SHA256 and documents the normalization rules. Executor, workspace
and toolchain directory prefixes were replaced by descriptive angle-bracket
tokens. Log line-end whitespace and excess terminal blank lines were removed;
no diagnostic lines were removed. Retained JSON hash
fields still describe the original files. Use the original-to-normalized map
when checking their committed counterparts. Token paths describe the original
roles and are not runnable paths.

This packet makes no full-root or import-aggregator build, CI, publication,
provenance ownership or issue-completion claim. The original runs identify
their checked individual files; they do not supply an independently frozen
entire Lean dependency/cache closure. Future import/CI registration remains
separate from these checks.
