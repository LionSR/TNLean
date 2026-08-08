# tenkz regression corpus

This directory is the compile-and-audit regression corpus for the tensor-network
diagram package. Run it from anywhere in the repository with:

```bash
scripts/tenkz_corpus.sh
```

The driver copies the whole directory to a temporary workspace, compiles every
standalone `.tex` file with the invocation from `docs/tenkz/HACKING.md`, and runs
`scripts/tenkz_audit.py` on every resulting `.tnlog`. The tracked corpus remains
clean.

## Render baselines

Add `--render` to compile and audit the corpus, then render every page of every
corpus PDF at 200 dpi:

```bash
scripts/tenkz_corpus.sh --render
```

The default output is `build/tenkz-corpus-render/`. Use `--render-dir DIR` to
name a different directory; relative directories are resolved from the
repository root, independent of the caller's working directory. The driver
reports the absolute output path and replaces it only after the complete
render succeeds. It refuses to replace a
nonempty directory unless that directory carries the ownership marker from an
earlier successful corpus render. A successful rerun therefore contains no
stale pages. Any failure before the completed directory swap leaves the last
baseline untouched. Once that swap succeeds, the new baseline is authoritative;
failure to remove the prior backup emits a warning with its exact retained path
but does not invalidate or roll back the completed render. Installers for the
same destination are serialized with a sibling lock, and the destination is
compared with its pre-render snapshot after the atomic move; if it changed while
rendering, the captured data is restored and the new baseline is refused.

Each fixture has a directory containing zero-padded `page-NNN.png` files.
`CENSUS.tsv` records the page count for every source, and `SHA256SUMS` records
the byte checksum of every PNG in stable path order. A baseline is complete
only when the reported PDF count equals the standalone corpus census and the
sum of `CENSUS.tsv` page counts equals the number of checksum entries.

For a behavior-preserving change, generate two baselines with the same TeX and
Poppler toolchain:

```bash
scripts/tenkz_corpus.sh --render --render-dir build/tenkz-before
# Apply the change.
scripts/tenkz_corpus.sh --render --render-dir build/tenkz-after
diff -u build/tenkz-before/CENSUS.tsv build/tenkz-after/CENSUS.tsv
diff -u build/tenkz-before/SHA256SUMS build/tenkz-after/SHA256SUMS
```

Both diffs must be empty. This is the render proof required by the recurring
simplification gate in issue #4158. A deliberately behavior-changing PR must
instead list every changed fixture/page from the checksum diff, compare the
corresponding before/after PNGs visually, and explain why each change is
expected. Preserve both generated directories until review is complete; do
not commit generated PNGs as source fixtures.

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

One package-internal probe deliberately creates no event records:
`plane_experiment.tex` uses tenkz dimensions, keys, or TikZ styles without
opening a tenkz environment. The driver names this exception explicitly and
rejects an empty `.tnlog` from every other fixture, so a broken event writer
cannot silently pass the corpus.

Every standalone fixture begins with a one-line `% Regression:` header and has a
`% Formula:` comment. Geometry-only fixtures state their geometry contract rather
than inventing a tensor identity.
