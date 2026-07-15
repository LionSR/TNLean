# Slides

Talk decks for the TNLean project. Each deck is a self-contained `.tex` file
that shares `preamble.tex` and `references.bib`.

Tensor-network figures use the repository-wide calculus in `tex/tn/`. The file
`tn_library_dark.tex` loads this calculus with `\usetikzlibrary{tn}`, overrides
the shared `\colorlet` palette slots, and then loads the six complete diagrams from
`tex/tn/tn_slide_catalogue.tex`. Tensor, map, state, expression, insertion,
wire, and port meanings remain those of the shared calculus.

## Naming

```
presentation<YYYYMMDD>_<topic>.tex
```

- `<YYYYMMDD>` — the presentation date, zero-padded (mandatory).
- `_<topic>` — a short `snake_case` slug, used when several decks share a date
  or the subject needs disambiguating. Omit it for a day's sole general-status
  deck (e.g. `presentation20260520.tex`).

Compiled PDFs are produced by `latexmk` (see `.latexmkrc`) and land in `build/`;
do not hand-name them.
