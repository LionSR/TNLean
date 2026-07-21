# tenkz regression corpus

This directory is the compile-and-audit regression corpus for the tensor-network
diagram package. Run it from anywhere in the repository with:

```bash
scripts/tenkz_corpus.sh
```

The driver copies the whole directory to a temporary workspace, compiles every
standalone `.tex` file with the invocation from `docs/tenkz/HACKING.md`, and runs
`scripts/tenkz_audit.py` on every resulting `.tnlog`. The tracked corpus remains
clean, and sibling inputs such as `modes_suite.inc` remain available.

## Provenance

The source is `handoff/corpus/` on branch `tenkz/handoff-artifacts`. The branch
contains 278 `.tex` files, although the handoff note reported 279. A current-main
census produced this adoption:

| Disposition | Count | Reason |
|---|---:|---|
| Included standalone fixtures | 257 | Compile with XeLaTeX, emit `.tnlog`, and pass `tenkz_audit.py` |
| Included support input | 1 | `modes_suite.tex` was renamed `modes_suite.inc`; it is included by `modes_test.tex`, not compiled alone |
| Excluded negative diagnostics | 7 | Deliberately exercise package errors or invalid arrow/species syntax |
| Excluded stale API probes | 12 | Historical spellings or parser experiments that no longer compile |
| Excluded non-tenkz probe | 1 | `exp_probe.tex` is a pure TikZ expansion experiment and emits no `.tnlog` |
| Source total | 278 | 257 + 1 + 7 + 12 + 1 |

`PROVENANCE.tsv` records the disposition of every source file. Negative probes
belong in dedicated tests that assert their expected diagnostics; they are not
passing corpus entries.

Four package-internal probes deliberately create no event records:
`geom.tex`, `p_pitch.tex`, `p_species.tex`, and `plane_experiment.tex`. They use
tenkz dimensions, keys, or TikZ styles without opening a tenkz environment. The
driver names these four exceptions explicitly and rejects an empty `.tnlog` from
every other fixture, so a broken event writer cannot silently pass the corpus.

Two included fixtures have documented presentation-only curations.
`gr_t7_coset.tex` moves its two gray action boxes 4 mm right so the
`k_x^{-1}` label clears the next box under the measured-overlap audit.
`plane_sweep1.tex` keeps its compact 0.45/0.55 region annotation visibly as
`R`, but uses `\scriptscriptstyle` so the adopted stress probe fits the compact
cell-corner clearance contract measured by the audit. Both formulas and diagram
topologies are unchanged.

Every standalone fixture begins with a one-line `% Regression:` header and has a
`% Formula:` comment. Geometry-only fixtures state their geometry contract rather
than inventing a tensor identity.
