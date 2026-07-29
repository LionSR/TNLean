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
  Product States volume, comprising exactly Chapters 1--12 through Symmetries
  and String Order, followed by an auxiliary channel-theory chapter.
- `src/print_ft_mps.tex` is the PDF entry point for that FT--MPS volume.
- `src/macros/` contains blueprint-specific macros and diagram commands.
- `src/references.bib` is the blueprint bibliography.
- `print/` and `web/` are generated outputs.

## Build and Check

Run these commands from the repository root:

```bash
lake build
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

This writes `blueprint/print/print12.pdf`, containing the Chapters 1--12
FT--MPS volume together with its auxiliary channel-theory chapter. The full
build remains at `blueprint/print/print.pdf`.

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
- `docs/prose_style.md`
- `docs/MATHLIB_doc.md`
