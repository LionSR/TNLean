# Hacking on tenkz

`LANGUAGE.md` is the public semantic contract.  `ARCHITECTURE.md` owns the
internal pipeline.  This file is the operational checklist for changing and
debugging the package.

## Fast build loop

Compile a standalone example from its own directory.  Keep the timeout: an
expl3 loop over an expanded `\q_no_value` otherwise looks like a slow run.

```sh
timeout 120 env TEXINPUTS="<repo>/tex/tenkz//:" \
  xelatex -interaction=nonstopmode -halt-on-error <file>.tex
```

Build the compact manual twice for contents and references:

```sh
python3 scripts/tenkz_manual_doctest.py
cd docs/tenkz
timeout 150 env TEXINPUTS="../../tex/tenkz//:" \
  xelatex -interaction=nonstopmode -halt-on-error manual2.tex
timeout 150 env TEXINPUTS="../../tex/tenkz//:" \
  xelatex -interaction=nonstopmode -halt-on-error manual2.tex
```

The generated language reference is
`chapters2/generated-language-reference.tex`.  Regenerate it from the
executable registry at `tex/tenkz/tenkz-language-registry.tex`; parser-facing
language code lives in `tex/tenkz/tenkz-language.code.tex`.  Do not edit the
generated file as an independent vocabulary list.  The manual has a short
fallback so a clean pre-generation checkout still compiles.

The RMP book has a separate driver and interface:

```sh
python3 scripts/tenkz_rmp.py check --id <target>
python3 scripts/tenkz_rmp.py check --section <section>
python3 scripts/tenkz_rmp.py check --all
python3 scripts/tenkz_rmp.py book --all
python3 scripts/tenkz_rmp.py render --all
python3 scripts/tenkz_rmp.py compare --all --source-root tex/RMP_TIKZ_SOURCE_CODE
```

Per-target verdicts are stored in `tests/tenkz/rmp/verdicts.toml`, one
stanza per target.  Any status may be recorded, including failure; the check
rejects lies, never gaps: a stale `case_sha256`, a `faithful` claim without a
second viewer and a verified pairing, or a `blocked` entry that names no
missing capability all fail, while recorded gaps merely appear in the book's
histogram.  A judged verdict pins the SHA-256 of its case; editing the case
stales exactly that verdict.

The ordinary 257-fixture corpus keeps its existing default interface:

```sh
scripts/tenkz_corpus.sh
scripts/tenkz_corpus.sh --render
```

Both suites may share lower-level helpers; neither frontend changes the
other's defaults.

## Audit and visual review

After compiling, audit the exact event stream used by the rendering and lint
the source:

```sh
python3 scripts/tenkz_audit.py <job>.tnlog
python3 scripts/tenkz_lint.py <source>.tex
```

Render every affected PDF and inspect it.  Exit status is not visual review.

```sh
mkdir -p tmp/pdfs/tenkz
pdftocairo -png -r 200 -singlefile <file>.pdf \
  tmp/pdfs/tenkz/<name>
```

Inspect labels, clipped ink, crossings, region contours, paired pages, and
section transitions.  A meaningful geometry change requires a fresh render.
Generated PDFs and PNGs are build artifacts, not committed source.

## Source and event checks

- Each figure states `Formula`, `Ink`, `Boundary`, `Source`, and
  `Capabilities` in its source header where the corpus format requires them.
- Structural capability tags name the public construct that owns the picture
  model. A `\tenkzkernel` case therefore carries `kernel`, even when its
  renderer contains a nested `tenkz` environment; `grid` is reserved for the
  grid surface without the kernel wrapper.
- A diagrammatic equation has the intended boundary signature on both sides.
- A matrix keeps two open virtual indices, a doubled-space map keeps four,
  and a scalar keeps none.
- The applied channel is `[sandwich, east={cup=$X$}]`; a west cup feeds the
  adjoint.
- Canonical sources do not use aliases, private control sequences, raw
  `tikzpicture`, whole-figure macros, or undocumented coordinate escapes.
- `\tndeclareatom` declarations have complete typed ports.  There is no
  public `\tndefine` mechanism.

## Architecture checks

Before editing a stage, read its five-line contract.  Maintain the direction

```text
language -> model -> style/atoms -> geometry -> dialect layout -> rendering -> events
```

Validation ends before measurement.  Rendering neither parses user syntax nor
changes topology.  Public names come from the executable registry; private
names follow `\__tenkz_<owner>_...:`.  Unsupported requested ink is a coded
error, never a warning followed by omission.

Until the S4 surface swap, kernel package loading is inert with respect to the
0.7 surface. `KERNEL-LOAD-SWEEP.md` records the binding and key-tree audit and
the regression that protects this boundary.

## expl3 and PGF traps

These mistakes have shipped bugs here.

1. Never expand `\q_no_value`.  Use the house accessor or a TF form of
   `\prop_get`.
2. Integer factors sit to the right of `*` in `\dimexpr`; prefer
   `\dim_eval:n`.  Do not put a leading decimal factor before a dimension
   macro in a pgfkeys value.
3. Double parameter tokens inside nested inline mappings: `##1` in the body
   of an `\int_step_inline:nnn` defined by another macro.
4. Normalize integer registers with `\int_eval:n` before using them as
   property keys.
5. User-input colons have catcode 12.  String-normalize before parsing
   `rows=`, `ports=`, and similar delimited forms.
6. `\use:e` passes `#` literally; do not double it there.
7. PGF keys split at literal commas and an unbraced value can be truncated at
   a second equals sign.  Brace values containing either character.
8. Expand integer registers explicitly in `\iow` event writes.
9. Picture IDs nest: the global UID and group-local current ID have different
   ownership.  An inline `\tnpic` must not clobber its parent.

## Geometry discipline

One base pitch controls the metric.  Repeated dimensions are named ratios.
Clearance uses the measured silhouette plus the single daylight separation;
do not add a constant that predicts what another pass will draw.

Useful focused regressions include:

```sh
python3 scripts/test_tenkz_face_ports.py
python3 scripts/test_tenkz_label_overlap.py
python3 scripts/test_tenkz_enclosures.py
```

Run the focused test while iterating, then the affected corpus or benchmark
section, then the repository gates appropriate to the change.

## Historical design records

Superseded design proposals, migration inventories, reviews, and 0.6
worklists live under `docs/tenkz/history/`.  They explain earlier decisions but
do not define current syntax.  Do not revive a spelling from history without
passing the extension gates in `LANGUAGE.md`.
