# tenkz — tensor-network diagrams from a description of the network

tenkz draws matrix product states, tensor trains, PEPS sheets, string
diagrams, and channel sandwiches from a statement of what the network is.
An author writes down the tensors, their indices, and how the indices meet;
the drawing measures where the ink goes. No coordinates and no lengths
appear in a picture source.

A picture is a set of typed records — atoms, wires, and marks — placed at
addresses inside a declared frame. The frame, which may be a flat grid, a
projected plane, or a circle, gives every address a position and its own
local axes, so an outward physical leg is the row's own normal rather than a
page direction, and a label's quadrant is a bearing in the host's axes. Every
index ends in exactly one of three ways: a bond to another tensor, a closure,
or a declared open leg. A pictured equation checks that its two sides expose
the same open indices.

Two tensors of a matrix product state, each with one open bond index and one
physical index:

```latex
\begin{tenkz}[cols=2]
  \tn[ports={180:virtual:$\alpha$, 90:physical:$i_1$}]{A} &
  \tn[ports={0:virtual:$\beta$, 90:physical:$i_2$}]{B}
\end{tenkz}
```

The two tensors are chained by `&`, the bond between them is drawn because
their adjacent index slots meet, and the open indices are the ones the source
names.

While drawing, tenkz writes an event stream recording the structure it
resolved — every atom, index, closure, and region. The stream is a
documented side surface: checking tools read it to confirm that a printed
picture and the contraction it claims to show agree.

## Requirements

- LaTeX2e with expl3, as distributed with TeX Live 2023 or later.
- pgf/TikZ.
- The `hobby` and `spath3` packages. Both provide TikZ libraries that tenkz
  loads at package load, and both are distributed separately from pgf; an
  installation missing either one fails when the package loads.

The regression corpus, the manual, and the reference figures are built with
XeTeX. pdfTeX and LuaTeX compile the language as well, and are not covered by
the project's tests.

## Installation

Unpack the archive and put its `.sty` and `.tex` files where LaTeX looks for
input, either in a local texmf tree under `tex/latex/tenkz/` or beside the
document. Then

```latex
\usepackage{tenkz}
```

loads the package and binds the diagram language: the `tenkz` and `tenkzeq`
environments and the body commands exist as soon as the package is loaded.

## Documentation

The manual states the language: every environment, command, and key, with a
picture for each and the failure each rejects. It is the contract the version
policy freezes. Manual and sources:
<https://github.com/LionSR/TNLean/tree/main/docs/tenkz>.

## Author and maintainer

Sirui Lu <sirui.lu@mpq.mpg.de>

tenkz is written for TNLean, a Lean 4 formalization of the mathematics of
tensor networks, and is developed in that repository:
<https://github.com/LionSR/TNLean>. Defect reports and questions belong in
its issue tracker: <https://github.com/LionSR/TNLean/issues>.

## License

Apache License, Version 2.0. The full terms are in the `LICENSE` file
distributed with this package, and every runtime file names the license in
its header.

## Version

Version 0.7, released 2026-07-22. The change record is in `CHANGES.md`, and
`CITATION.cff` and `tenkz.bib` carry the citation metadata.
