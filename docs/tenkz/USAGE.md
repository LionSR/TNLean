# tenkz — Phase-0 usage guide

Everything in this guide is implemented and render-verified today. The full
design rationale is in [DESIGN.md](DESIGN.md); the critique of the old
library is in [REVIEW.md](REVIEW.md). Compileable examples live in
`tex/tenkz/examples/` — `gallery.tex` shows every construction on one page.

## Loading

```latex
\usepackage{tenkz}          % engine: xelatex
```

The package lives in `tex/tenkz/`; compile with
`TEXINPUTS="tex/tenkz//:" xelatex …` (the blueprint build will wire this
in via `latexmkrc`).

## The contraction grid: `tenkz` and `\tnpic`

A diagram is a grid: **rows are layers, columns are sites**. Bonds between
horizontally adjacent cells are implicit. The picture is a math atom — its
wire axis sits on the math axis, so `=`, `\sum`, `\otimes` compose diagrams
with no glue.

```latex
% a 3-site periodic MPS word: one body line
\begin{tenkz}[periodic, physical=up, bond label={$D$ at 1-2}]
  \tn[up=$i_1$]{A} & \tn[up=$i_2$]{A} & \tn[up=$i_3$]{A}
\end{tenkz}
```

```latex
% the gauge equation, with '=' on the wire axis
\[
  \begin{tenkz}[physical=up]  \tn[up=$i$]{B}  \end{tenkz}
  \;=\;
  \begin{tenkz}[physical=up]
    \tnX{X} & \tn[up=$i$]{A} & \tnX{X^{-1}}
  \end{tenkz}
\]
```

Typed rows pair facing physical legs automatically — an `op` row's down
legs join the next row's up legs, column by column:

```latex
% transfer map                          % expectation-value window
\begin{tenkz}[sandwich]                 \begin{tenkz}[rows={ket, op, bra}]
  \tn{A} \\                               \tn{A} & \tn{A} & \tn{A} \\
  \tn*{A}                                 \tn[mpo]{O} & \tn[mpo]{O} & \tn[mpo]{O} \\
\end{tenkz}                               \tn*{A} & \tn*{A} & \tn*{A}
                                        \end{tenkz}
```

`\tnpic[keys]{body}` is the command form — legal inline in running math:

```latex
$\mathcal{E}_A(X)=\sum_{i}\,\tnpic[sandwich, inline]{\tn{A^i} \\ \tn*{A^i}}\,(X)$
```

### Environment keys

| Key | Meaning |
|---|---|
| `rows={ket\|bra\|op\|wire, …}` | typed layer declarations; suffix `:operator` hues the row's virtual wire red (MPO layer), `:fused` renders it doubled |
| `physical=up\|down\|updown\|none` | single-row sugar for `rows=` |
| `sandwich` | `rows={ket,bra}` with paired legs |
| `periodic` | trace closure (single row: below; two rows: above and below) |
| `bond label={$D$ at 1-2}` | label an addressed bond |
| `align=<row>` | put that row on the math axis (default: midline) |
| `pitch=<dim>`, `compact`, `inline` | metrics; profiles are scale factors |
| `tensor style=dot\|box` | per-picture glyph policy (see below) |

### Cell commands

| Command | Meaning |
|---|---|
| `\tn[opts]{A}` / `\tn*[opts]{A}` | tensor (`*` = conjugate, overlined label). Opts: `dot`, `box`, `pill`, `mpo` (skin), `wide=k` (span k columns), `up=<math>`/`down=<math>` (leg-tip labels), `label pos=<compass>`, `label shift={dx,dy}`, `no legs` |
| `\tnX{X}` | matrix on the wire (gauge insertion; height-pinned capsule) |
| `\tnfuse[rows=2, combined=west\|east]{V}` | fusion bar spanning two wire rows; combined leg leaves as a doubled stub |
| `\tndots` | the canonical ellipsis cell (interrupts the wire) |
| `\tnghost{}` | invisible spacer; the wire passes through |
| `\tnspan[brace above\|brace below]{k}{label}` | brace over k columns starting at the current cell; clearance adapts to legs and labels |
| `\tncut{S}` | labeled dashed bipartition line after the current column |

## Tensor-style modes

Both schools, one source. `dot` (default) draws beads with labels placed
outside by the auto-quadrant rule; `box` inscribes the label:

```latex
\tnset{tensor style=box}          % document-wide
\begin{tenkz}[tensor style=box]   % or per picture
```

Explicit per-cell skins always override the policy. All inscribed glyphs
share one strut, so boxes labelled `A`, `T_g`, `A^{(2)}` have one height.
See `examples/modes-demo.tex` for the same suite rendered both ways.

## Labels never overlap ink

Leg-tip, bond, brace, and bead labels sit in reserved bands derived from
the metric system; bead labels pick a free compass quadrant automatically.
When you disagree with a choice: `label pos=south west`,
`label shift={2pt,0pt}`.

## Commutative diagrams: `tenkzcd` and `\tntree`

Pentagon equations are commutative diagrams, not contractions:

```latex
\begin{tenkzcd}[polygon=5, radius=34mm]
  \tntree{(((a\,b)_x\,c)_y\,d)_e} &
  \tntree{((a\,(b\,c)_u)_y\,d)_e} &
  \tntree{(a\,((b\,c)_u\,d)_w)_e} &
  \tntree{(a\,(b\,(c\,d)_v)_w)_e} &
  \tntree{((a\,b)_x\,(c\,d)_v)_e}
  \tnarrow[from=1, to=2]{F^{abc}_y}
  \tnarrow*[from=1, to=5]{F^{ab,c,d}_e}   % * = label on the other side
  … 
\end{tenkzcd}
```

`\tntree{word}` builds a fusion tree from a parenthesization word; the
subscripts are internal charges. Leaves and charges are single characters
or braced groups. Without `polygon=`, `tenkzcd` wraps plain tikz-cd, and
cells may contain `\tnpic{…}`/`\tntree{…}`.

## Lattice windows and regions: `tenkzlattice`

Regions are **cell-set data**, never hand-traced polygons:

```latex
\begin{tenkzlattice}[rows=4, cols=4, boundary legs]
  \tnregion[slot=selected,  name=R, label=$R$]{(1-3, 1-3)}
  \tnregion[slot=secondary, outline, label=$S$, label at=south west]{R - (2,2)}
  \tnedge[distinguished]{(2,3)-(2,4)}
  \tnsite[removed]{(2,2)}
\end{tenkzlattice}
```

Cell sets: rectangles `(r1-r2,c1-c2)`, singletons `(r,c)`, registered
names, `+`/`-` for union/difference. The tracer computes rectilinear
hulls with notches — and true holes (a removed interior site renders as a
ring, its dot and bonds omitted). Slots: `selected`, `secondary`,
`complement`, `collar`; `outline` suppresses the fill. Grids up to 12×12.

## Free placement: `tenkzfree`

The escape hatch for genuinely non-grid diagrams (MERA, lassos) — and the
one tier with runtime port-type checking:

```latex
\begin{tenkzfree}
  \tnput[ports={east:virtual, north:physical}]{a}{(0,0)}{A}
  \tnput[ports={west:virtual}]{b}{(14mm,0)}{B}
  \tnjoin{a.east}{b.west}                              % ok: virtual-virtual
  \tnjoin[route=curve, out=90, in=90, label=T]{a.north}{b.north}
\end{tenkzfree}
```

Joining a physical port to a virtual one is a compile error. Routes:
`straight`, `hv`, `vh`, `curve` (with `out=`/`in=`); `fused` doubles the
stroke.

## Practical notes

- Every picture writes semantic events to `\jobname.tnlog` (atoms, bonds,
  traces, joins) — the audit layer consumes these; you can ignore the file.
- Inside `align` and other `&`-alignment contexts, wrap the grid body in a
  macro defined outside the alignment (the `&` catcode clash is inherited
  from pgf-matrix; same caveat as quantikz).
- Restyle globally with `\tnset` and the style names in DESIGN.md §4
  (`tensor`, `bond`, `label`, `region selected`, …) — never with raw
  colors or line widths at call sites.
