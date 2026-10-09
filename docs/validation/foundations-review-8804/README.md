# Exact-counting review repair: focused blueprint validation

The two chapter leaves at source checkpoint
`d975c515fdebefb092325f9fe6c4d7b50dc9daac` pass focused PDF and static HTML
validation. [The machine-readable report](render-validation.json) records
the source hashes, generated artifact hashes, declaration inventory, labels,
warnings and visual inspection.

- All 43 public declarations in seven `Graph*.lean` modules have exactly one
  blueprint owner, one generated declaration-list entry and one link in each
  rendered format. Reverse coverage is complete. The modules total 1,202 lines;
  five private helpers remain private.
- The leaves contain 20 mathematical entries, 15 proof sketches and 35 checked
  markers. All 34 labels, 22 ordinary references and 39 dependency occurrences
  resolve locally. There are no duplicate HTML IDs, missing anchors, renderer
  error sentinels, or final PDF overfull, missing-glyph or unresolved-reference
  diagnostics.
- All seven retired square declarations and both retired labels are absent
  from blueprint references throughout the immutable source snapshot. The
  generic indicator proof and generated dependency graphs retain only the
  target-domination, target-exclusion and chain-growth dependencies; the stale
  diamond-budget edge is absent.
- All eight PDF page images were directly inspected. The affected mathematical
  content occupies PDF pages 3–7 (printed pages 2–6). The shortened ambient-count
  discussion, exact diamond constants, indicator specialization and scalar-series
  citation are legible, with no clipping, overlap or missing glyphs. Title,
  contents and bibliography pages were also checked.
- Neither leaf contains a Tenkz, TikZ or commutative-diagram picture, so a picture
  sweep is not applicable.

The source snapshot is extracted from Git objects, not copied from the working
tree. All 634 selected files are checked against their immutable Git blobs.
The focused fixture changes only its content router and removes an unrelated
Fundamental-Theorem dependency-graph subset. Production Lean, TeX, repository
routers and provenance ledgers are not modified by these scripts.

The full build log preserves intermediate unresolved-reference messages from
the first compilation passes; the final TeX log is clean. Inherited
`pdftex.map`/`kanjix.map` warnings and a duplicate `page.1` destination remain in
the PDF conversion log. The vector imager is unavailable in this environment;
there are no pictures to convert. Every labeled destination and declaration
link was independently checked in the finished PDF.

## Reproduction

Use Python with `texra-blueprint` 0.3.8, `plasTeX` 3.1,
`leanblueprint` 0.0.20 and the repository reader-check dependencies, plus
XeLaTeX, BibTeX, latexmk and Poppler. Configure the pinned Tenkz package on
`TEXINPUTS` and a writable, valid TeX format cache before compiling. The scripts
do not install tools or invoke Lean/Lake.

Choose a new persistent output directory outside the checkout. Run preparation
from the repository root; `RENDER_OUT` below denotes its absolute path.

```sh
python3 docs/validation/foundations-review-8804/prepare_render.py \
  --root . --revision d975c515fdebefb092325f9fe6c4d7b50dc9daac \
  --out "$RENDER_OUT"
```

Run these commands from `$RENDER_OUT/blueprint/src` after loading the prepared
TeX environment:

```sh
latexmk -xelatex -interaction=nonstopmode -halt-on-error print.tex \
  > ../../pdf-build.log 2>&1
python3 - <<'PY'
from pathlib import Path
import re
numbers = iter(range(1, 100))
Path('web.bbl').write_text(re.sub(
    r'\\bibitem\{',
    lambda _: r'\bibitem[' + str(next(numbers)) + ']{',
    Path('print.bbl').read_text(),
))
PY
plastex -c plastex.cfg web.tex > ../../web-build.log 2>&1
pdftotext -layout print.pdf ../../print.txt
mkdir -p ../../pdf-pages
pdftoppm -r 110 -png print.pdf ../../pdf-pages/page
```

From the repository root, run the static verification:

```sh
python3 docs/validation/foundations-review-8804/verify_render.py \
  --root . --out "$RENDER_OUT"
```

The initial result explicitly leaves visual inspection pending. Inspect every
page image, then supply a JSON record through `--visual-review` containing
`status: "passed"`, a description of the inspected content and a
`page_image_sha256` object mapping every `page-N.png` to its SHA-256 hash.
The verifier accepts that record only when all image hashes match. The committed
report contains the direct inspection record for this run.

## Limits

This is a focused chapter render, with static HTML checks. It does not claim a
full-book build, a live-browser/MathJax or mobile check, fresh Lean execution,
remote declaration-page availability, current CI, publication or merge. Native
and axiom verification are recorded separately. The scalar-series estimate is
an auxiliary result; physical commutator propagation, full Lemma 4.1, the area
law and PEPS approximation are not certified by this render.

Only text scripts and this report are committed. Generated PDFs, HTML, page
images, source snapshots and raw logs remain outside Git in the persistent
validation output.
