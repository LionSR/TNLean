# Fixed chronological sources: verification evidence

The 19 public declarations in `declarations.json` were verified at source
revision `6246647741ce41a55a3897329336055330dd7e6f`. They formalize the
common sources and the two separated contractions used in the proof of Theorem 5.2 of the pinned polynomial-PEPS
manuscript, `04-compression.tex`, lines 253–267 and 342–434.

The surviving positions are the original ordered source occurrences having an
affected endpoint. Their dimensions and finite enumeration are independent of
all branch labels. Every actual partial branch is recovered by preparing its
normalized vectors in these common spaces, followed by allowed operations
containing no sources. The source vector at each position is proved to be the
original vector selected by the label of its owning gate. The argument compares
ordered source records and distinguishes repeated occurrences.

The direct selective-factorization theorem starts with an actual allowed word.
Its free positions contain every crossing source. It constructs two contractions
on the entire free input space before arbitrary free source vectors are supplied,
and recovers the original operator on its original vectors. It assumes no source
normal form and imposes no bound on private memory dimensions.

These statements do not assert the corrected-position trace-norm estimate,
random-source compression, or the physical protocol construction.

All three exact-source modules compiled with package options and warnings as
errors, without diagnostics. `direct-build.log` records commands, source hashes,
artifact hashes and durations. These are direct Lean checks using immutable
predecessor artifacts, not a Lake build or a CI timing measurement. No package
cache was changed. The only local elaboration option is `Elab.async false` on the
dependent selective-factorization declaration; the default heartbeat limit is
retained.

The importing audit checks all 19 explicit public declarations and reports only
`propext`, `Classical.choice`, and `Quot.sound`. Compressed manifests identify all
4,361 imported artifacts. The first generated audit
used one excessively long printed name; its namespace was shortened and only the
audit was repeated. Proof sources were unchanged. Final verification compared
all committed proof bytes and rechecked every imported artifact hash.

The blueprint records exact declaration coverage, source synchronization,
dependency-graph inspection, formatting, focused PDF/web rendering, and browser
checks. It distinguishes these from a compiled full-root declaration check.
The separate regression directory records the actual nonempty-source examples
and their own exact verification scope.

Run the packaged canonical provenance check for the ten source-gate
contributions, comprising 342 declarations:

```sh
uv run --no-project --with jsonschema==4.26.0 python \
  docs/provenance/evidence/8769-fixed-chronological-sources/replay.py \
  --root . --upstream-root /path/to/openai-math
```

This checks recorded evidence, exact source bytes, manuscript labels, notices,
and identifier collisions. It does not recompile Lean or repeat the unrelated
historical license audit. Without `--upstream-root`, manuscript labels are
explicitly not rechecked. All 19 declarations are independent formalizations;
no upstream Lean proof text was reused.
