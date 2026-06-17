# Slides

Talk decks for the TNLean project. Each deck is a self-contained `.tex` file
that shares `preamble.tex` and `references.bib`.

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
