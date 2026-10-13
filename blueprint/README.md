# Blueprint

This directory contains the mathematical blueprint for TNLean.  The blueprint is
the reader-facing account of the formalization: it states the definitions,
lemmas, and theorems in mathematical language and links them to the
corresponding Lean declarations with `\lean{...}` and `\leanok` tags.

## Layout

- `src/` contains the LaTeX source.
- `src/chapter/` contains one file per chapter.
- `src/content.tex` is the chapter router for the full Tensor Network Theory
  blueprint.
- `src/content_ft_mps.tex` contains the separate Fundamental Theorem of Matrix
  Product States volume, comprising the tensor-network chapters through
  Symmetries and String Order.
- `src/print_ft_mps.tex` is the PDF entry point for that FT--MPS volume.
- `src/macros/` contains blueprint-specific macros and diagram commands.
- `src/references.bib` is the blueprint bibliography.
- `print/` and `web/` are generated outputs.

## Build and Check

Run these commands from the repository root:

```bash
lake build
python3 scripts/fetch_tenkz.py
cd blueprint
leanblueprint checkdecls
leanblueprint pdf
leanblueprint web
```

`leanblueprint checkdecls` should be run after adding or changing `\lean{...}`
tags.  The PDF and web builds regenerate `blueprint/print/` and
`blueprint/web/`.

Build the separate FT--MPS volume from the repository root:

```bash
./scripts/build_blueprint_ch01_12.sh
```

This writes `blueprint/print/print12.pdf`, containing the focused FT--MPS
volume. The full build remains at `blueprint/print/print.pdf`.

## Writing Conventions

Blueprint prose should be mathematical prose.  Avoid Lean-specific explanations
in visible text; the `\lean{...}` tag supplies the link to the formal
declaration.  Maintainer notes about proof status, local formalization choices,
or paper-gap documents should be written as LaTeX comments unless they are part
of the mathematical statement being presented to readers.

When a result is claimed to formalize a source theorem, the blueprint statement
must match the source hypotheses.  If the current Lean theorem has extra
hypotheses, the source theorem should not be marked as fully formalized until a
source-faithful statement exists.

The detailed style rules are in:

- `docs/blueprint_style_guide.md`
- the `lean-conventions` skill (prose_style, MATHLIB_doc references)

## Shared figures

`src/figures/<name>.tex` holds tensor-network displays that the blueprint and
external documents (such as diagrammatic notes on the source papers) typeset
from one source. The print build, the web build and the notes all compile the
same file, so a figure may use only tenkz, `macros/diagrams.tex`,
amsmath/amssymb, `\ket`, `\bra`, `\C`, `\spn`, and its own label macros.
`src/figures/README.md` states the full file contract.

- **Naming.** A figure is named after the label of the entry that owns it,
  without the kind prefix (`def:peps_tensor` becomes `figures/peps_tensor.tex`),
  with `_a`, `_b` when an entry holds several displays. A figure made for the
  notes only uses a paper prefix such as `polypeps_` or `arealaw2d_`.
- **Using a figure in a chapter.** Write the literal
  `\input{figures/<name>}` on its own line where the display stood, inside the
  entry. Never put it inside a `tenkzequation` and never wrap it in a macro: the
  web build, the tenkz sweep and the diagram tests (through
  `scripts/blueprint_tex_tree.py`) see only the literal form. Keep a whole
  display, its panels and joiners in one figure file.
- **Label macros.** Where a note needs other letters, a figure routes a label
  through `\tnl<Tag><Role>` and declares the blueprint's literal as the default
  with `\providecommand` at the top of each picture body that uses it (the web
  build compiles each body on its own). Hosts override it with `\newcommand`.
- **External documents.** Put `blueprint/src` on `TEXINPUTS` without `//`, load
  `\usepackage{tnleanfigures}` after the document's own packages, and write
  `\tnfigure{<name>}`. `src/tnleanfigures.sty` loads tenkz (the pin when
  `$TENKZ_ROOT/tex/tenkz//` is on `TEXINPUTS`), `macros/diagrams.tex`, a
  centred `tenkzequation`, and the four label macros with the meanings in
  `macros/common.tex`. Do not load `macros/common.tex` in a note: it clashes
  on `\theorem` and `\Tr`.
- **Checks.** `python3 scripts/test_shared_figures_diagram.py` checks the file
  contract, every `\input{figures/...}` in the chapters and appendices, the
  sync of `tnleanfigures.sty` with `macros/common.tex`, and compiles every
  figure through `tnleanfigures.sty` with pdflatex. CI also runs `tenkz_lint`
  on `src/figures/*.tex`.
