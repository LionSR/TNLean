# Slides

Talk decks for the TNLean project. Each deck is a self-contained `.tex` file
that shares `preamble.tex` and `references.bib`.

Tensor-network figures use the native `tenkz` package in `tex/tenkz/`.
`preamble.tex` loads the package and `tn_library_dark.tex` rebinds only its
semantic colour slots for the dark Beamer theme.  Each slide keeps its complete,
nonempty diagram body beside the formula and source comments that determine its
mathematical meaning, so a deck can customize a figure locally without changing
a hidden catalogue.  Tensor, wire, port, contraction, and boundary meanings
remain those of `tenkz`.

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
