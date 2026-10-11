# Shared figures

Each `<name>.tex` here holds one tensor-network display that the blueprint and
external documents (the diagrammatic notes) typeset from the same source.

- **Name.** The owning entry's label without its kind prefix
  (`def:peps_tensor` gives `peps_tensor.tex`), with `_a`, `_b` when one entry
  holds several displays. Figures that exist only for the notes use a paper
  prefix (`arealaw2d_`, `polypeps_`, or `tn2d_` when both notes use them).
  The directory is flat; names match `[a-z0-9_]+.tex`.
- **Header.** `% Figure <name>.`, `% Owner: chapter/<file>.tex (<label>)` or
  `% Owner: none (note-only figure).`, `% Used by: ...`, then the provenance
  comments the diagram tests read (`Source:`, `Ink-to-index:`, boundary
  signatures) and `% Label macros: ...` when the figure has any.
- **Body.** Exactly one top-level `tenkzequation`, `tenkz` or `tikzcd` (or a
  `center` holding one `tenkz` or `tikzcd`) at column 0, ASCII only, no blank
  line inside. Keep a whole display (panels and
  joiners) in one file. No `\label`, `\lean`, `\uses`, `\leanok`, refs, cites,
  theorem environments, raw `tikzpicture`, definitions or `\input`.
- **Macros.** Only tenkz, `macros/diagrams.tex`, amsmath/amssymb, `\ket`,
  `\bra`, `\C`, `\spn`, and the figure's own `\tnl<Tag><Role>` label macros.
  Declare each label macro with `\providecommand` as the first lines of every
  picture body that uses it; the default is the blueprint's original literal.
- **Use.** Chapters write the literal `\input{figures/<name>}` on its own line
  inside the entry, never inside a `tenkzequation`. External documents load
  `\usepackage{tnleanfigures}` and write `\tnfigure{<name>}`.

`scripts/test_shared_figures.py` enforces these rules and compiles every
figure through `tnleanfigures.sty`. See also the "Shared figures" section of
`blueprint/README.md`.
