# tenkz 0.5

<!-- Companion to USAGE.md (Phase-0 basics). Manual v2 supersedes both. -->

## Boundaries

Open virtual indices are the default and render as protruding stubs. A matrix
product looks like a matrix: `\tn{A} & \tn{B}` gives `—●——●—`. No open legs
means a scalar.

| Key | Effect |
|---|---|
| `boundary=open` | stubs at each wire row's ends (default) |
| `boundary=none` | sealed ends, for closed objects |
| `periodic` | trace closure |
| `rows={op:open, ket:none}` | per-row override |
| `west label=$\alpha$`, `east label=$\beta$` | boundary index labels |

Each picture writes its boundary signature to `.tnlog`:

```
boundary|…|virtual-west=2|virtual-east=2|physical-up=1|physical-down=0
```

Two sides of an equation denote the same object only if their signatures match.

## Cups

`close west` / `close east` join adjacent row pairs by a bend — the ket-to-bra
tie of sandwich objects. `periodic` closes a row to itself; a cup contracts two
rows. `close east={$\rho^R$}` puts a fixed-point dot on the apex.

```latex
% rho_n = Tr_{env} |psi><psi|: cups tie the virtual indices,
% rho^R / rho^L cap the bends, physical legs stay open.
\begin{tenkz}[rows={ket:nopair, bra}, close west={$\rho^R$}, close east={$\rho^L$}]
  \tn{A} & \tndots & \tn{A} \\
  \tn*{A} & \tndots & \tn*{A}
\end{tenkz}
```

`nopair` keeps a row pair's physical legs open. `layer sep=` tunes the row gap.

The canonical channel spellings:

```latex
\begin{tenkz}[sandwich]                    % E_A: four open legs, a map
\begin{tenkz}[sandwich, close west={$X$}]  % E_A(X): two open legs, a matrix
```

## Atoms

| Key | Effect |
|---|---|
| `\tn[wires=2]{U}` | one atom spanning two wire rows; also on `\tnX` |
| `\tn[pill, wide=2, legs at={1,2}]{U}` | physical legs at chosen columns |
| `\tnskip` | a hole: wires stay open across the gap |
| `trace=physical` | close each up leg into its own down leg around the glyph |
| `\tn[tri=l]{A_L}`, `tri=r` | canonical-form isometry triangles |
| `rows={op:dir right}`, `bond dir=`, `\tnjoin[dir]` | directed bonds: arrow out = vector space, in = dual |

## Lattice and planes

Cells address as `(row, col)` or `(row, col, sheet)`: rows and columns count
from 1; sheets count from 0 (bra) upward (ket = 1). An unaddressed cell in a
sheeted picture lives on the ket sheet.

| Key | Effect |
|---|---|
| `\tnregion[slot=, outline, inset=, label=, label at=, name=]{cells}` | region from cell-set algebra; `inset=1` draws a nested boundary one unit tighter |
| `\tnedge{(r,c,h)-(r',c',h')}` | distinguished edge, any sheet |
| `plane=flat\|oblique\|slab`, `plane slant=`, `plane rise=`, `plane lean=` | the projected frame; bonds shear, glyphs and labels stay upright |
| `col vector=`, `row vector=`, `sheet vector=` | expert frame: arbitrary projected basis vectors |
| `sheets=2, pairing` on tenkzlattice | the double layer as one lattice |
| `\begin{tenkzplanes}[rows=, cols=, open={(1,2)}, trace={(1-4,4)}]` | ket-over-bra double layer; `open` cells keep stubs; `trace` cells close by the wrap loop — the marginal `Tr_traced` |

## Examples

The acceptance tests compile with `TEXINPUTS=tex/tenkz//: xelatex`:
`boundary_test.tex`, `cups_test.tex`, `atoms_test.tex`, `plane_test.tex`, and
the RMP reproductions `hard01…hard12_v3.tex` beside their `ref_*.png`
originals. Every source states its formula in `%` comments.

## Gaps

Per-side boundary control, a bare identity-wire atom, `combined=` on `wires=k`
glyphs, inter-sheet closures, directed signatures, mirrored `tri=` closures.
Tracked for 0.6.
