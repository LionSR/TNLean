# TNLean Tensor-Network TikZ Library — Consolidated Final Specification

**Package name: `tenkz`; this specification targets v1.0** (the shipped package stands at v0.6 — see `CHANGES-0.6.md` for the grammar as implemented). Winning architecture: **Design 1 (tenkz)** — 2 of 3 judges (judge-tufte, judge-maintainer), cross-design tally 179 vs 176 (Quartet). Quartet's signature assets are grafted in wholesale; tenkz's judge-flagged defects are fixed in this document. This spec is the implementation contract.

---

## 0. Synthesis record: grafts integrated and conflicts resolved

### 0.1 Grafts (all judge-converged items are in this spec)

| # | Graft | Source | Where it lands |
|---|---|---|---|
| G1 | Slice contract: every environment yields a box with declared axis pinned to the math axis (`\fontdimen22\textfont2`) + published border anchors + picture id | Quartet | §1.4 |
| G2 | Typed row declarations `rows={ket\|bra\|op[:fused]}` with automatic adjacent-layer leg pairing (closes the B7 pairing ambiguity) | Quartet | §2.1, B7 |
| G3 | Fused-bond doubled-stroke wire skin (RMP index-bundle convention) | Quartet | §2.1, §4 |
| G4 | Directed virtual bonds (`bond dir=`, MPO orientation) | tncalc | §2.1 |
| G5 | Internal-charge fusion-tree grammar `(((a\,b)_x c)_y d)_e` (Quartet spelling, per judge-maintainer) | Quartet/tncalc | §2.3, B5 |
| G6 | Addressed bond labels `bond label={$D$ at 1-2}` | tncalc | §2.1, B1 |
| G7 | `pos=auto` label-quadrant algorithm (quadrant derived from the atom's free side, one clearance constant) | tncalc | §4.3 |
| G8 | Typed-port extension protocol `\tndeclareatom{kind}{glyph=…, ports={w:virtual,…}}` (anchors alone are not enough) | tncalc | §2.6 |
| G9 | Event-graph isomorphism migration gate (old vs new typed contraction graph per entry; waivable with one-line justification) | Quartet | §5.6, §6 |
| G10 | Role-stability audit advisory ("selected bound to R in fig 3 but T in fig 5") | Quartet | §5.4 |
| G11 | Transfer-map canonicality advisory (isomorphic double-layer drawn without `sandwich` is flagged) | Quartet | §5.4 |
| G12 | Cross-engine drift check: multiset of canonical graph hashes compared between print and web builds | tncalc | §5.5 |
| G13 | Externalization-vs-audit policy (flag event at `\begin{document}`; CI owns the authoritative `.tnlog`) | tncalc | §5.5 |
| G14 | Theme-may-only-bind-colors enforced structurally (build check rejects geometry keys in theme scope) | Quartet | §4.1 |
| G15 | Adopted compile-and-audit corpus with render baselines | tnplain | §5.7 |
| G16 | Literal-zero migration exit scan | tnplain | §6 |
| G17 | Lint ban on literal `...`/`\ldots` inside picture bodies (must be `\tndots`) | tnplain | §5.7 |
| G18 | Region-tracer day-1 fallback (fill mode = per-cell rounded squares; outline restricted to simply-connected sets until the notch algorithm matures) | tnplain | §1.3, §6 |
| G19 | Governance: measured public API surface + "a new command requires a new grammatical class; a new builder key requires three existing figures it shortens" | tnplain | §2.7 |
| G20 | Explicit `tenkzequation` row keeps SVG diagram atoms outside MathJax while retaining copyable operator text | tnplain | §1.5 |
| G21 | Sugar contract: every sugar and builder expands to primitives with byte-identical event streams | tncalc | §5.2 |
| G22 | "Why this is a command and not a key" printed per command in the reference chapter | Quartet | §7 |
| G23 | Genre-ownership table (every brief use case mapped to exactly one sub-language) + Knuth-grade geometry-appendix format (constant, value, derivation, printed motivation) | Quartet | §4.4, §7 |
| G24 | Deliberate type-error demonstration in the tutorial | tncalc | §7 |
| G25 | Raw tikz-cd (with `\tnpic` objects) documented as first-class fallback while polygon mode matures | tnplain via judge-author | §2.2, §7 |
| G26 | Benchmark corrections: B4's blocked pill carries the combined physical index $i_1\cdots i_L$; B5's trees display internal charges | judge-tufte | §3 |

### 0.2 Conflicts between judges, resolved

1. **Winner split** (judge-author → Quartet; judges tufte + maintainer → tenkz). Resolved for tenkz on tally and 2/3 majority. Judge-author's preference is substantively honored: Quartet's five distinguishing assets (G1, G2/G3, G9, G10/G11, G23) are grafted, and his four concrete tenkz defects are fixed here — the `\tnfuse` signature contradiction (§2.1), the command-vs-key doctrine contradiction (§2.7), the polygon-mode honesty problem (§2.2), and the compressed Phase-1 hump (§6, split into scripted sub-batches with two gates).
2. **Engine** (author: xelatex forecloses Lua for the hull tracer; tufte + maintainer: xelatex avoids a book-wide typography gamble). **Resolved: keep xelatex end-to-end** (print and corpus = xelatex; web = xelatex → .xdv → dvisvgm). Two judges explicitly scored this as a tenkz advantage. The tracer is written in expl3 over bounded grids (≤ 12×12) with tnplain's day-1 fallback (G18). Escalation path is Open Question 1.
3. **Row pairing mechanism** (maintainer offered `rows=` typing *and/or* `\contract{±n}`). **Resolved: `rows=` typing only, no new command.** Adjacent-layer pairing is a row-policy default; the per-cell escape is a `pair=+1|-1|none` key on `\tn`. This keeps the API surface flat and is consistent with the doctrine in §2.7.
4. **Line-budget governance** (author wanted tnplain's CI cap; tnplain's own 800-line cap was busted by its own table, per judge-maintainer). **Resolved: measure the API, not the line count.** The shipped surface has five public environments across four sub-languages (the fifth is the `tenkzplanes` preset), 17 exported commands, and 143 leaf keys. The recurring simplification gate records that census; per-file line budgets remain advisory. A quantikz-scale grid engine cannot honestly promise 800 lines.
5. **Migration regression mechanism** (pixel diff vs event-graph isomorphism). **Resolved: both.** Pixel diff with a whitelisted intentional-fix list (visual critique items) *and* the iso gate (G9); the iso gate is waivable per figure with a one-line justification, same discipline as paper-gap notes.

---

## 1. Final architecture

### 1.1 Native file plan

```
tenkz.sty                 user entry point; version; loads all layers
tenkz-core.code.tex       L0  /tenkz/ pgfkeys tree; two-layer theme/semantic styles COMPLETED
                              for all styles (closes the 14/31 gap); semantic hue table;
                              metric system: ONE pitch (11mm) + 38 documented ratios (§4.4);
                              event stream v2 (.tnlog, expl3 iow, per-picture ids, currfile src);
                              port-type registry (virtual/physical ONLY — morphism deleted);
                              theme scope guard (rejects geometry keys in themes, G14)
tenkz-grid.code.tex       L2a the tenkz environment: expl3 +b body capture, tikz-cd/pgf-matrix
                              layout, expandable cell commands, implicit bond wiring, typed
                              rows= engine with auto-pairing (G2), fused-bond skin (G3),
                              directed bonds (G4), deferred decoration pass (trace arcs,
                              leg pairing, \tnfuse, \tnspan, \tncut, addressed bond labels)
tenkz-cd.code.tex         L2b tenkzcd: grid mode = tikz-cd verbatim + house arrow styles +
                              TN objects; polygon=n mode = native polar placement of named
                              nodes, arrows rendered through tikz-cd's arrow-style vocabulary;
                              \tntree bracketing parser with internal charges (G5)
tenkz-lattice.code.tex    L2c tenkzlattice: rows×cols site grid (dot or bond-only skins),
                              per-side openings, traces, and two-sheet cups; cell-set
                              algebra; rectilinear hull tracer WITH notches (fallback G18);
                              \tnregion / \tnedge / \tnsite on semantic slots; tenkzplanes
                              is the maintained multi-sheet preset over this grammar
tenkz-free.code.tex       L2d tenkzfree: tikzpicture preset + \tnput/\tnjoin; the only place
                              runtime port-type assertions fire (grid languages are type-safe
                              by construction)
scripts/tenkz_audit.py    .tnlog v2 consumer: canonicalizer, invariants, iso gate, drift check
scripts/tenkz_corpus.sh   adopted compile-and-audit corpus and optional render baseline (G15)
scripts/tenkz_lint.py     source lint: \ldots ban in picture bodies (G17), raw-ink lint for
                          tenkzfree and any residual raw tikzpicture
blueprint/src/Packages/tenkz_pic.py
                          plasTeX module: renders the four languages, tenkzplanes preset,
                          and \tnpic generically;
                          per-body content-hash SVG cache; explicit equation rows (G20)
docs/tenkz/manual2.tex    the citable quantikz-style manual (§7)
docs/tenkz/HACKING.md     operational build, audit, and visual-review guidance
```

### 1.2 Layering discipline

- **Primitives (L0/L1):** styles, hues, metrics, typed shapes, event writer. Never called by users; shared substrate of all four sub-languages — one `\tnset{tensor/.append style=…}` restyles every picture in the book.
- **Combinators (cell/body commands):** each both draws and emits typed events; all sugar expands to primitives with byte-identical event streams (G21), so hand-composed and sugared figures are indistinguishable to the audit and equally decoratable.
- **Environments (L2):** each sub-language owns its layout engine and event dialect. L2a–d may not import each other's drawing primitives; they share only L0/L1.

### 1.3 Sub-language relations and the bridge object

`\tnpic{…}` is the bridge: a robust, saveboxed, overlay-free command form of the `tenkz` environment producing a self-contained math atom. It is legal (a) inline in running math (B8) and (b) as a cell object in `tenkzcd` (B5). The cd language therefore contains TN pictures without sharing the contraction grammar; lattice sites use their own `site=dot|none` policy. All four languages write to one `.tnlog` with a `lang=` tag.

Region hulls: the tracer computes rectilinear outlines with notches from cell-set expressions in expl3. Day 1 ships with G18 fallbacks (`fill` mode as per-cell rounded squares; `outline` restricted to simply-connected sets) so B6-family figures render before the notch algorithm is final.

### 1.4 The slice contract (G1)

Every environment and `\tnpic` yields a **slice**: a TeX box whose declared axis (`align=` row, default the midline of the wire rows) is pinned to the math axis (`\fontdimen22\textfont2`), with published border anchors (N/S/E/W + corners) and a picture id in the event stream. Consequences: plain `=`, `\to`, `\Rightarrow`, `\sum`, and `\left(…\right)` compose diagrams with zero glue commands; tikz-cd cells, complete lattice windows, and running math all receive the same box type. Embedded slices are opaque except axis + border in v1 (port re-export across an embedding is a documented v2 extension).

### 1.5 Engine and web pipeline

One engine end-to-end: **xelatex** for print and the adopted corpus; **xelatex → .xdv → dvisvgm** for web SVG (dvisvgm reads xdv natively). The library is engine-neutral internally (no unicode-math dependency). plasTeX registers the native environments + `\tnpic` as verbatim-captured, standalone-compiled SVG units with per-body content-hash caching — one edited figure invalidates one SVG, not the whole book. Blueprint equations containing diagram atoms use the explicit `tenkzequation` text-mode row (G20): every picture remains its own SVG outside MathJax, while equality signs, arrows, and other operator text remain selectable.

---

## 2. Complete public API

**Surface: five public environments across four sub-languages + 17 commands + 143 documented leaf keys.** The recurring gate counts the surface (G19). Every command's reference entry prints its "why not a key" justification (G22).

### 2.1 `tenkz` — the contraction grid

`\begin{tenkz}[⟨keys⟩] …&…\\ … \end{tenkz}` — rows = layers, columns = sites; math atom per the slice contract.

Environment keys:

| Key | Meaning |
|---|---|
| `rows={⟨ket\|bra\|op\|wire⟩[:fused],…}` | Typed row declarations (G2). `ket` = physical legs up; `bra` = down; `op` = up+down; `wire` = none. **Pairing rule:** adjacent facing legs auto-join column-by-column (an `op` row's down legs join the next row's up legs); outermost legs stay open. `:fused` renders that row's virtual wire in the fused doubled-stroke skin (G3). Default: one `wire` row. |
| `physical=up\|down\|updown\|none\|paired` | Single-row sugar and per-row list form; `physical={updown,up}` ≡ `rows={op,ket}`. Retained for one-row chains. |
| `sandwich` | ≡ `rows={ket,bra}` with paired legs and midline axis. Literal sugar; expands to identical events (G21). |
| `periodic` | Virtual trace closure arc (deferred pass, racetrack geometry). |
| `trace=physical` | Close one centred upper port into one centred lower port at each site; asymmetric or multi-port faces remain open with a diagnostic. |
| `bond label={⟨math⟩ at ⟨c⟩-⟨c'⟩}` | Addressed bond label (G6); bare `bond label=⟨math⟩` = first bond. |
| `bond dir=left\|right` or `{⟨dir⟩ at ⟨c⟩-⟨c'⟩,…}` | Directed virtual bonds, MPO orientation (G4); scalar applies to all bonds. |
| `align=⟨row⟩` | Axis row (non-integers allowed); default = midline of wire rows — the multi-row `=` defect is closed with no per-call key. |
| `pitch=⟨dim⟩`, `compact`, `inline`, `hue=⟨name⟩`, `name=⟨id⟩` | Metrics, profile, semantic hue, picture identity. |
| `row sep=`, `column sep=`, `&[len]`, `\\[len]` | pgf-matrix passthrough. |

Cell commands (expandable; legal only inside `tenkz`/`\tnpic`):

- `\tn[⟨keys⟩]{A}` / `\tn*[⟨keys⟩]{A}` — THE tensor atom; `*` = conjugate skin. Keys: shape (`dot`,`box`,`circle`,`tri=l|r`,`pill`,`diamond`,`mpo`,`peps`), `wide=⟨k⟩`, `wires=⟨k⟩` (span k rows, terminating each row's wire — quantikz `\gate[2]`), face ports `up at=`, `down at=`, `west at=`, `east at=` (`center` or local span slots), physical-leg labels `up=`,`down=`, leg suppression `no legs`, `pair=+1|-1|none` (per-cell override of the row pairing policy — the resolution of conflict 3), `hue=`, `on wire`, `name=`.  The older `legs at=` assigns the same slot list to both physical faces unless a face-specific key overrides it.
- `\tnX[⟨keys⟩]{X}` — matrix ON the wire (gauge insertion; open ring, arity 2, no physical leg, narrow column). Documented as ≡ `\tn[on wire]{X}`; earns its two-letter spelling as the second-most-frequent atom (quantikz's `\ctrl` precedent). Symmetric by construction: it occupies its own cell on either side.
- `\tnfuse[⟨keys⟩]{V}` — **fixed signature (single optional argument).** n-to-1 trivalent map. Keys: `span=⟨k⟩` (wire rows spanned, default 2) and the same `west at=` / `east at=` face data.  A centred face is the one fused port; the opposite local row slots are the separate ports.  A sparse list, such as `{1,3}`, draws, contracts, and counts only those slots.  `combined=west|east` remains the compatibility spelling (default `west`). *Why a command:* it rewrites wire topology (merges rows) — a different grammatical class from `\tn`, whose contract is to terminate the wires of its own rows.
- `\tndots[⟨keys⟩]` — the canonical ellipsis cell: interrupts the implicit wire, typesets dots on the wire axis. The only legal ellipsis (G17 lints the literals).
- `\tnghost{A}` — invisible sizing atom.
- `\tnspan[⟨keys⟩]{⟨cols⟩}{⟨label⟩}` — column-range decoration anchored at the current cell: `brace above|below` or measured `box`, with `label pos=` at a compass point, corner, or centre.  A box fits the rendered member glyphs, including ellipses and asymmetric row ranges, while legs remain outside it.  Unknown modes, including the removed `shade` spelling, fail closed.
- `\tncut[⟨keys⟩]{⟨label⟩}` — labeled dashed bipartition line after the current column (quantikz `\slice`).

### 2.2 `tenkzcd` — commutative diagrams

`\begin{tenkzcd}[⟨keys⟩] … \end{tenkzcd}`

- **Grid mode** (default): *is* tikz-cd — all its keys and the full `\arrow` grammar pass through — plus house arrow/label styles (`cd arrow`: 0.40pt, open head, boundary-clipped with named standoff) and TN objects via `\tnpic`/`\tntree`.
- **Polygon mode** (`polygon=⟨n⟩, radius=⟨dim⟩`): n `&`-separated cells placed as named nodes on a regular n-gon (vertex 1 on top, clockwise); `\tnarrow[from=⟨i⟩, to=⟨j⟩]{⟨label⟩}` between vertex names (`\tnarrow*` puts the label on the other side; the spec first wrote this in tikz-cd's `\arrow` grammar — the shipped grammar is `\tnarrow`). **Honesty clause (fixes the judge-author flag):** polygon mode implements node *placement* only; arrow drawing, shortening, and label sides reuse tikz-cd's arrow-style vocabulary — it does not reimplement an arrow engine. **Documented first-class fallback (G25):** a raw `tikzcd` grid with `\tnpic`/`\tntree` objects is sanctioned whenever a layout exceeds polygon mode; the manual shows the pentagon both ways.
- **Typed-map mode** (`maps`): a matrix of objects joined along the fixed left-to-right composition axis. A map has the form
  `\tnarrow[from={(r,c)}, to={(r,c+1)}, role=⟨role⟩]{⟨name⟩}` or
  `\tnarrow[from={(r,c)}, to={(r,c+1)}, species=⟨species⟩]{⟨name⟩}`;
  `fused` selects the fused line type, and `\tnarrow*` places the name on the opposite side. Every map must have either a role or a declared species. The line style records the map's type; the label records only the map itself. There are no arrowheads: the order of the objects determines the order of composition. Vertical maps, reverse maps, and maps that skip an object column lie outside this grammar.

Map declarations are literal top-level commands after the matrix objects.
Grouping or nesting a declaration is an error: the layout pass does not enter
an opaque object merely to discover geometry that the outer matrix would own.

The object-column gap is uniform across the small multiples and is measured
from their widest opaque map-name band: its width plus two daylights, with
`0.34·pitch` as the floor. Thus a long or superscripted name cannot erase the
adjacent objects. An explicit `column sep=` remains an authoritative opt-in
override and may deliberately undercut this automatic clearance.

Typed-map rows belong to the categorical diagram language, not to the tensor-network language. Their vertices are mathematical objects and their joining strokes are maps, not contracted indices. A `\tnpic` occurring in an object cell remains an opaque mathematical object; the adjacent typed-map stroke does not acquire tensor ports or enter its contraction graph. The modes `maps` and `polygon` are disjoint, while ordinary grid mode retains the complete tikz-cd arrow grammar.

A family is written as small multiples: one complete domain--codomain row for each member, with the same number of object columns in every row. A finite family is displayed in full, rather than by selected representatives. Parameters may remain symbolic when the displayed row asserts a formula uniformly over all their values. The matrix is a math object and requires no separate sizing mode. In an ordinary TeX document it may occur in displayed or running mathematics. In blueprint chapter source a single `tenkzcd` is a top-level block outside `$...$` and `\[...\]`; a row with operators or sibling pictures uses `tenkzequation`. A genuine float still uses `figure`.

For the CPSV refinement, the middle-subspin Hilbert space is

\[
  \mathcal H^{\Omega}_{k,h}
  =\bigoplus_l(B_k^R\otimes B_l^L)\otimes(B_l^R\otimes B_h^L).
\]

The neighboring operator and the normalized active density on this space are

\[
  \Omega_{k,h}=\bigoplus_l
    (\eta_{k,l}\otimes\eta_{l,h}),
  \qquad
  \widehat\Omega_{k,h}=\frac{1}{a_kb_h}\Omega_{k,h}
  \quad(a_kb_h\ne0).
\]

For a nonzero finite-dimensional Hilbert space $H$, write
$\tau_H=(\dim H)^{-1}I_H$ for its faithful uniform density.

The total completed density is

\[
  \overline\Omega_{k,h}
  =\begin{cases}
      \widehat\Omega_{k,h},&a_kb_h\ne0,\\
      \tau_{\mathcal H^{\Omega}_{k,h}},&a_kb_h=0.
    \end{cases}
\]

Thus
$\overline\Omega_{k,h}\in\operatorname{End}(\mathcal H^{\Omega}_{k,h})$
and $\operatorname{tr}(\overline\Omega_{k,h})=1$. A typed-map vertex records
an operator space in the refinement displays below, not a coordinate
expression, a carrier Hilbert space, or a density acting on that space.
Introduce the five matrix algebras

\[
\begin{aligned}
  \mathcal A_2
  &=\operatorname{End}\!\left(
      \left[\bigoplus_j(B_j^L\otimes B_j^R)\right]^{\!\otimes2}\right),
  &
  \mathcal A_{\partial}
  &=\operatorname{End}\!\left(\bigoplus_{k,h}B_k^L\otimes B_h^R\right),\\
  \mathcal A_{\eta}
  &=\operatorname{End}\!\left(
      \bigoplus_{k,h}\bigl[(B_k^L\otimes B_h^R)\otimes
        (B_k^R\otimes B_h^L)\bigr]\right),
  &
  \mathcal A_{\Omega}
  &=\operatorname{End}\!\left(
      \bigoplus_{k,h}\bigl[(B_k^L\otimes B_h^R)\otimes
        \mathcal H^{\Omega}_{k,h}\bigr]\right),\\
  \mathcal A_3
  &=\operatorname{End}\!\left(
      \left[\bigoplus_j(B_j^L\otimes B_j^R)\right]^{\!\otimes3}\right).
\end{aligned}
\]

The global refinement is the composition

\[
  \mathcal A_2
  \xrightarrow{\mathcal T_0}
  \mathcal A_{\partial}
  \xrightarrow{\mathcal T_1}
  \mathcal A_{\Omega}
  \xrightarrow{\mathcal T_2}
  \mathcal A_3.
\]

On a $(k,h)$-summand, $\mathcal T_0$ traces out the factors
$B_k^R\otimes B_h^L$,
$\mathcal T_1$ sends $X$ to $X\otimes\overline\Omega_{k,h}$, and
$\mathcal T_2$ reorders the subspin factors into the three output sites.
Consequently $\mathcal T=\mathcal T_2\mathcal T_1\mathcal T_0$. In `tenkzcd`
this is written as follows.

The companion global maps have types
$\mathcal S_0:\mathcal A_3\to\mathcal A_{\partial}$ and
$\mathcal S_2:\mathcal A_{\eta}\to\mathcal A_2$. On a fixed outer pair,
$\mathcal S_0$ traces the full direct sum $\mathcal H^{\Omega}_{k,h}$; the
sectorwise map $\mathcal S_0^{(k,l,h)}$ instead fixes $l$ before taking the
partial trace.

```latex
% Formula: T_0 : A_2 -> A_partial, T_1 : A_partial -> A_Omega, and
% T_2 : A_Omega -> A_3. Ink: every blue stroke denotes a channel, its label
% names the stage, and composition runs left-to-right.
\[
\begin{tenkzcd}[maps, species={channel}]
  \mathcal A_2 &
  \mathcal A_{\partial} &
  \mathcal A_{\Omega} &
  \mathcal A_3
  \tnarrow[from={(1,1)}, to={(1,2)}, species=channel]{\mathcal T_0}
  \tnarrow[from={(1,2)}, to={(1,3)}, species=channel]{\mathcal T_1}
  \tnarrow[from={(1,3)}, to={(1,4)}, species=channel]{\mathcal T_2}
\end{tenkzcd}
\]
```

### 2.3 Math / CD objects

- `\tnpic[⟨keys⟩]{⟨grid body⟩}` — command form of `tenkz`; the inline-math and cd embedding vehicle. Identical grammar and keys; `inline` switches to text-style metrics with the axis on the inter-layer midline.
- `\tntree[⟨keys⟩]{⟨bracketing⟩}` — fusion tree from a parenthesization word **with internal-charge subscripts** (G5): `(((a\,b)_x\,c)_y\,d)_e` labels internal edges x, y and the total charge e. Module trees carry type marks for mixed wire types; `grow=down|up`. Kills the 5 frozen fusion-tree macros: the bracketing *is* the data.

### 2.4 `tenkzlattice` — lattice-region schematics

`\begin{tenkzlattice}[rows=, cols=, site=dot|none, boundary=open|none, west|east|north|south=open|none|trace|cup|cup=⟨m⟩, physical=up|updown|none, pitch=, compact, inline, tensor style=, species=, frame=flat|oblique|slab, plane slant=, plane rise=, plane lean=east|west, sheets=, sheet sep=, pairing, open=, trace=, outer legs=, col|row|sheet vector={x,y}] … \end{tenkzlattice}`

- `\tnregion[slot=selected|secondary|complement|collar, label=⟨math⟩, label at=⟨anchor⟩, outline, name=⟨R⟩]{⟨cell set⟩}` — cell-set algebra: `(r1-r2, c1-c2)` rectangles, `(r,c)` singletons, `+`/`-` union/difference, named sets (`R - (2,2)`). Hull traced automatically with notches (fallback per G18). Slots bind document-wide semantic colors; role stability is audited (G10).
- `\tnedge[distinguished|none|role=operator|marked|extra|passive|style=⟨TikZ⟩|label=⟨math⟩]{(r,c[,h])-(r',c'[,h'])}` — lattice-edge decoration, suppression, or label, on its own layer (under sites, over wires).
- `\tnsite[removed|role=operator|marked|extra|passive|label=⟨math⟩]{(r,c[,h])}` — single-site removal or decoration.

The environment body is a live execute-once customization layer. It records any number of `\tnregion`, `\tnedge`, and `\tnsite` commands before the lattice draw passes consume them; a stacked lattice never replays the body once per sheet.

### 2.5 `tenkzfree` — sanctioned free placement

`\begin{tenkzfree}[⟨keys⟩] … \end{tenkzfree}` — a themed tikzpicture preset for genuinely non-grid diagrams (MERA, lassos, star tensors, ad hoc contractions).

- `\tnput[⟨keys⟩]{⟨name⟩}{(x,y)}{A}` — place any L1 glyph with typed anchors.
- `\tnjoin[name=⟨name⟩, route=straight|hv|vh|arc, trace=above|below|right, label=, dir=, fused]{⟨a.E⟩}{⟨b.W⟩}` — typed connection; an optional name makes the measured route and its label available to a region.
- `\tnregion[group|slot=selected|secondary|complement|collar, outline, label=, label pos=, name=]{⟨members⟩}` — a measured enclosure over comma-separated names of earlier `\tnput` atoms, named `\tnjoin` routes, or named regions.  The public command dispatches to this name-set grammar in `tenkzfree` and to cell-set algebra in `tenkzlattice`.

The free environment body is an execute-once customization layer: atoms,
joins, and regions remain ordinary body commands, and the shared semantic
TikZ styles (`group region`, `region selected`, and the other region slots)
may be extended with `/.append style` without bypassing measured geometry.
Enclosure fills occupy automatically depth-ordered background layers; an
outer named region is behind every named region it contains.  Outlines and
labels remain above every fill, so nesting preserves both semantic colors and
boundary ink, while later members cannot be covered.  The historical
`/tenkz/region` key family remains the lattice option path for compatibility;
public `\tnregion` dispatch does not rename document-level lattice extensions.

### 2.6 Setup and extension

- `\tnset{…}` — the single pgfkeys front door: themes, pitch, hue table, house policies, `⟨style⟩/.append style` for the §4 style table.
- `\tndefine\Cmd[⟨n⟩]{⟨body⟩}` — named reusable diagram = plain macro over an environment body; chapter-local allowed; hashed and logged. The sanctioned way to name a figure; no registration, no catalogue.
- `\tndeclareatom{⟨kind⟩}{glyph=⟨pgf code⟩, ports={w:virtual, e:virtual, ph:physical}, …}` — the documented "I need one more glyph" protocol (G8). Port declarations are **typed**, not bare anchors; declared kinds are immediately legal as `\tn` shapes and `\tnput` glyphs.

### 2.7 The command-vs-key doctrine (restated, fixing the contradiction)

A command exists **iff** it introduces a new grammatical class: atom (`\tn`), on-wire atom (`\tnX`), topology-rewriter (`\tnfuse`), wire-interruption token (`\tndots`), null atom (`\tnghost`), column-range decoration (`\tnspan`), inter-column token (`\tncut`), generator (`\tntree`), bridge (`\tnpic`), region/edge/site data payloads, free-tier place/join, and the three setup verbs. **Keys may vary an atom's extent** (`wide=`, `wires=`) **or its policy** (`pair=`) **but never its grammatical class.** `wires=k` does not contradict this: a `\tn` spanning k rows still terminates every wire it touches; `\tnfuse` merges rows into one wire — a different class. New commands require demonstrating a new class in the manual's justification section; new builder keys require three existing chapter figures they shorten (G19). Everything else must be a key.

---

## 3. Final end-user LaTeX: benchmarks B1–B8

**B1 — 3-site periodic MPS word, physical labels, trace closure, addressed bond label**

```latex
\begin{tenkz}[periodic, physical=up, bond label={$D$ at 1-2}]
  \tn[up=$i_1$]{A} & \tn[up=$i_2$]{A} & \tn[up=$i_3$]{A}
\end{tenkz}
```

**B2 — Gauge equation, `=` on the wire axis**

```latex
\[
  \begin{tenkz}[physical=up]
    \tn[up=$i$]{B}
  \end{tenkz}
  \;=\;
  \begin{tenkz}[physical=up]
    \tnX{X} & \tn[up=$i$]{A} & \tnX{X^{-1}}
  \end{tenkz}
\]
```

**B3 — Transfer map: ket/bra double layer, joined physical legs**

```latex
\[
  \E_A \;=\;
  \begin{tenkz}[sandwich]
    \tn{A} \\
    \tn*{A}
  \end{tenkz}
\]
```

`sandwich` ≡ `rows={ket,bra}` + pairing + midline axis. This is THE canonical transfer-map drawing; the sanctioned opaque alternative is `\tnX[pill]{\E_A^{\,n}}` on a doubled wire, and the manual's canonical-spelling table states when each is correct. The audit flags isomorphic hand-drawn copies (G11).

**B4 — Blocking (corrected per G26: combined physical index on the blocked site)**

```latex
\[
  \begin{tenkz}[physical=up]
    \tn[up=$i_1$]{A}\tnspan[brace below]{4}{L\text{ copies}} &
    \tn[up=$i_2$]{A} & \tndots & \tn[up=$i_L$]{A}
  \end{tenkz}
  \;=\;
  \begin{tenkz}[physical=up]
    \tn[pill, wide=2, up={$i_1\cdots i_L$}]{A^{(L)}}
  \end{tenkz}
\]
```

**B5 — Fusion-tree pentagon (corrected per G26: trees display the internal charges the F-arrows reference)**

```latex
\begin{tenkzcd}[polygon=5, radius=34mm]
  \tntree{(((a\,b)_x\,c)_y\,d)_e} &
  \tntree{((a\,(b\,c)_u)_y\,d)_e} &
  \tntree{(a\,((b\,c)_u\,d)_w)_e} &
  \tntree{(a\,(b\,(c\,d)_v)_w)_e} &
  \tntree{((a\,b)_x\,(c\,d)_v)_e}
  \tnarrow[from=1, to=2]{F^{abc}_y}
  \tnarrow[from=2, to=3]{F^{a,bc,d}_e}
  \tnarrow[from=3, to=4]{F^{bcd}_w}
  \tnarrow*[from=1, to=5]{F^{ab,c,d}_e}
  \tnarrow*[from=5, to=4]{F^{a,b,cd}_e}
\end{tenkzcd}
```

**B6 — PEPS 4×4 window: dangling legs, shaded R, notched S = R∖{v}, distinguished edge**

```latex
\begin{tenkzlattice}[rows=4, cols=4, boundary legs]
  \tnregion[slot=selected,  name=R, label=$R$]{(1-3, 1-3)}
  \tnregion[slot=secondary, outline, label=$S$, label at=south west]{R - (2,2)}
  \tnedge[distinguished]{(2,3)-(2,4)}
  \tnsite[removed]{(2,2)}
\end{tenkzlattice}
```

**B7 — Zipper / pulling-through (rewritten with typed rows, fixed `\tnfuse` signature; pairing is now unambiguous: the `op` row's down legs join the `ket` row's up legs by the G2 rule)**

```latex
\[
  \begin{tenkz}[rows={op, ket}]
    \tnfuse[span=2]{V} & \tn[mpo]{O}\tnspan[brace above]{3}{n} & \tndots & \tn[mpo]{O} \\
                       & \tn{A}                                & \tndots & \tn{A}
  \end{tenkz}
  \;=\;
  \begin{tenkz}[rows={op, ket}]
    \tn[mpo]{O}\tnspan[brace above]{3}{n} & \tndots & \tn[mpo]{O} & \tnfuse[span=2, combined=east]{V} \\
    \tn{B}                                & \tndots & \tn{B}      &
  \end{tenkz}
\]
```

`\tnfuse[span=2]{V}` spans both wire rows: two east stubs feed the layer wires, one combined wire exits west in the fused doubled-stroke skin (mirrored via `combined=east` on the RHS). Axis defaults to the midline, so `=` aligns across both sides with no key.

**B8 — Inline transfer-map atom inside `\sum` in running math**

```latex
Positivity of the transfer map follows termwise, since
$\E_A(X)=\sum_{i}\,\tnpic[sandwich, inline]{\tn{A^i} \\ \tn*{A^i}}\,(X)$
and each summand is a congruence.
```

Ordinary TeX may use this inline atom directly. Blueprint web source keeps it out of `$...$` and places display-adjacent diagram equations in `tenkzequation` (G20). The wrapper renders each picture independently and leaves its intervening operator text selectable. **&-free fallback for hostile contexts** (`align`, footnotes, externalization): state the same row explicitly with top-level siblings rather than placing an image inside MathJax input.

---

## 4. Theme, style, hue, and metric tables

### 4.1 Theme contract

Two-layer split: **semantic styles** (what a mark means) bind to **theme slots** (how it looks). A theme may bind **colors only**; the build check rejects geometry keys in theme scope (G14). Dark theme recolors — it never reshapes (open ring stays open). Themes: `print` (default), `dark` (also serves slides — the Slide* interface is deleted).

### 4.2 Style table (complete; all restylable via `\tnset{⟨name⟩/.append style=…}`)

| Style | Applies to | Ink | Notes |
|---|---|---|---|
| `tensor` | `\tn` atoms | 0.55pt stroke, solid fill | solid dot / box / pill / diamond skins |
| `conjugate tensor` | `\tn*` | 0.55pt | mirrored skin, barred label |
| `on-wire matrix` | `\tnX`, insertion ring | 0.55pt solid ring | opaque paper fill; never dashed micro-outline |
| `mpo tensor` | `\tn[mpo]` | 0.55pt | operator-layer skin |
| `peps tensor` | lattice sites, `\tn[peps]` | 0.55pt | leg geometry fixed in L1 (no double-stroke defect) |
| `fusion map` | `\tnfuse` | 0.55pt | trivalent glyph |
| `tree junction` | `\tntree` nodes | dot ≥ 0.9mm | absolute print floor, about 4.7 wire widths |
| `bond` | virtual wires | 0.55pt | identical stroke to physical (type = direction) |
| `fused bond` | `:fused` rows, `\tnfuse` output, `\tnjoin[fused]` | doubled 0.55pt | RMP index-bundle convention (G3) |
| `physical leg` | leg stubs | 0.55pt | length 0.38·pitch |
| `bond arrow` | `bond dir=` marks | 0.55pt head | MPO orientation (G4) |
| `trace` | `periodic`/`trace=` arcs | 0.55pt | racetrack outside the measured silhouette plus 0.15·pitch daylight |
| `cut` | `\tncut` | 0.40pt dashed | |
| `brace` | `\tnspan[brace *]` | 0.40pt | annotation ink |
| `group region` | `\tnspan[box]`, `\tnregion[group]` | 0.40pt dashed, no fill | one meaning and one measured renderer in grid and free tiers |
| `ellipsis` | `\tndots` | label ink | the only legal dots |
| `label` | all labels | — | quadrant via `pos=auto` (G7) |
| `region selected` | `slot=selected` | 0.80pt outline + fill | shaded R in B6 |
| `region secondary` | `slot=secondary` | 0.80pt outline | |
| `region complement` | `slot=complement` | 0.80pt dashed, gray | |
| `region collar` | `slot=collar` | 0.80pt | |
| `distinguished edge` | `\tnedge` | 0.80pt accent | own layer |
| `distinguished vertex` | `\tnsite` | accent | |
| `typed map` | `tenkzcd[maps]` edges | role/species bond style, headless | the label names the map; order is the fixed axis |
| `cd arrow` | tenkzcd arrows | 0.40pt, open head | never confusable with 0.55pt wires |

### 4.3 Semantic hue table (document-wide meanings)

`ink` (near-black / off-white), `action` (accent — gauge/insertion emphasis), `marked` (distinguished edges/vertices), `extra` (secondary emphasis), `passive` (gray/complement), plus the four region slots above. Labels reference hues by name only; `pos=auto` derives the label quadrant from the atom's free side with the single `label clearance` constant (G7) — the anti-wander algorithm.

### 4.4 Metric system (Knuth-grade; the geometry appendix prints each row in this format — G23)

One base: `pitch = 11mm` (display). Derived constants (name, value, motivation):

| Constant | Value | Motivation |
|---|---|---|
| `layer sep` | 0.80·pitch | double layers read as layers, not as two chains |
| `physical leg` | 0.38·pitch | a labeled leg clears the bond label at script size |
| `virtual stub` | 0.45·pitch | long enough to read as an open index, shorter than a bond so a dangling end is never mistaken for a contraction |
| `daylight` | 0.15·pitch beyond the measured silhouette | pure separation keeps return and annotation ink from fusing with the ink it skirts |
| `label clearance` | 0.12·pitch | one constant for every quadrant (G7) |
| `junction diameter` | ≥ 0.9mm (about 4.7 × the 0.55pt wire width) | the absolute print floor keeps a junction distinct from a wire crossing |
| `region margin` (`\tenkz@r@latticemargin`) | 0.27·pitch | strictly < pitch/2 so single-site notches read; > glyph radius so hulls never clip glyphs |
| `compact` / `inline` | 0.8 / 0.62 scale on pitch | profiles are one scale factor, not parallel constant lists — literals cannot bypass them |
| `map column gap` | max(0.34·pitch, widest map-name band + 2·daylight) | the floor keeps a short composition compact; measured opaque label ink clears both adjacent objects without budgeting glyphs; explicit `column sep=` remains an opt-in override |
| `map row gap` | 0.50·pitch | adjacent small multiples remain distinct without figure-scale leading; `row sep=` overrides it |

---

## 5. Audit design

### 5.1 Event stream v2 (`.tnlog`)

Every environment emits `picture|id=N|lang=L` at `\tenkz@beginpicture` (the
only writer of `lang=`; `L` is one of `grid`, `cd`, `lattice`, `free`),
then dialect events carrying an explicit `picture=N` back-reference.
`warning`, `label-use`, `ink-use`, `bbox`, `glyph-geometry`, and
`wire-geometry` events are cross-cutting (any dialect may emit them).
`label-anchor-site` is the corresponding lattice-only relation for a region
corner label and its deliberately adjacent site or sites. These records, like
`boundary`, are stripped from a picture's content before dialect and
empty-picture checks run — they are diagnostics and derived data, not topology.
Every library-owned `tn label`
style use emits `label-use` and one live-anchor shape
`bbox|picture=...|class=label|id=...|xmin=...|xmax=...|ymin=...|ymax=...|shape=...|radius=...`.
Coordinates are integer scaled points. Every core glyph skin emits a paired
`ink-use` and exact live-node geometry after removing evaluated outer
separation. The geometry includes the final live half-stroke (`stroke=`):
rectangles use their visible extents, circles use their visible extents and
radius, rounded rectangles use their visible extents and stroked corner radius,
and canonical triangles use their three centerline corner anchors plus the
exact polygon-edge and vertex stroke band. Audited glyphs must have a live fill;
draw-only customizations fail closed because their interior is not ink. Labels
likewise use their visible live support after removing outer separation. A
transparent text-only label emits the materialized text-box rectangle, excluding
both inner and outer separation. A fill-only label emits
`shape=rect,radius=0`; a sharp rectangular fill with a round-join stroke emits
`shape=roundrect,radius=<half-stroke>`. The exact label contract requires
positive text opacity; an active fill also requires positive fill opacity, and
an outline without a fill fails closed because its ring is not representable by
this schema. Rounded-corner fill paths are rejected because they can leave
text-box corners uncovered. Audited labels and glyphs permit translation but reject
non-identity linear node transforms, and labels reject non-rectangle shapes.
The snapshot observes the real post-adjustment outer separation and the actual
path-use support, so the exact geometry is independent of stroke/fill color and
of positive opacity. It fails closed for effects outside that model: non-round
line joins, dashed or double strokes, zero opacity on active ink, shading,
fading, path pictures, clipping, or multiple path-use/mode/outer-adjust passes.
Typed maps additionally emit sibling object geometry and one exact
`wire-geometry` record: the stroke-expanded endpoint rectangle minus the exact
visible filled-and-stroked support of its owning label. Typed-map measurement
requires that inner label to use an opaque `tenkzPaper` fill, independently of
the transparent general `tn label` default. The record names that
label by its exact emitted bbox id in `cut-id`. For another measured label and
a cut wire, an overlap with the owning label is reported once as a label-label
overlap and suppresses the consequent wire diagnostic; when the two labels are
disjoint, intersection with the outer wire rectangle is equivalent to
intersection with the visible difference. The audit
rejects a strict
intersection between a label and any sibling glyph/wire node, permits
tangency, and rejects any label, glyph, or wire-node use without matching
geometry. A lattice `label-anchor-site` relation permits only the corner
label's intersection with a circle centered at a declared adjacent site;
all other sibling intersections remain errors. Typed-map path restyling may
change colour, positive width, opacity,
or ordinary/double stroke, but fails closed for path-local affine transforms,
nonzero shortening, a path-local cap change, decoration, and pre/post actions;
those effects invalidate the anchor-derived horizontal-rectangle model. The
captured softpath must contain exactly one move followed by one horizontal line,
with no curve, close, rounded-corner, or extra-path tokens, and arrow tips are
unsupported. The captured live width must be positive: zero-width PDF hairlines
and negative widths have no faithful rectangle in this schema. Clipping, path
or scope fading, path-picture ink, and a terminal blend mode other than
`normal` also fail closed. Blend-mode validation observes inherited state and
permits a later map style to restore `normal` before the path is used.
The event records the integer shaft centre `y`, full live width `outer`, and
full actually empty inner gap `inner`; the audit constructs the transverse
boundaries as exact half-scaled-point values. Thus `inner=0` denotes one solid
outer rectangle, while a positive value denotes two exact horizontal rails
separated by a centered gap. A positive raw PGF inner width
is preserved as that gap only when its inner stroke is exactly `tenkzPaper`
at full live stroke opacity. A coloured inner stroke, or translucent paper
over the outer stroke, remains visible ink and is normalized to `inner=0`.
The raw inner width must be nonnegative and smaller than the outer width, and
the resulting geometry still belongs to the same single ink owner.

Arbitrary TikZ paths are deliberately outside this sibling-node contract. In
particular, a label may annotate its parent bond, and curved or decorated paths
cannot be replaced by whole-path axis-aligned boxes without inventing non-ink
collisions. A path contributes to this audit only when its renderer exposes
exact visible support, as typed maps do with a solid horizontal wire rectangle
minus their opaque label.

The table below is generated from the `\tenkz@event{...}` call
sites themselves (grep `tenkz@event{` across `tex/tenkz/*.code.tex`),
not hand-maintained prose — the two drift out of step otherwise.

| Dialect | Content event kinds | Source module |
|---|---|---|
| `grid` | `atom`, `bond`, `faceports`, `pairleg`, `hole`, `cup`, `boundary`, `phtrace`, `pairtrace`, `trace`, `hooks`, `span` | `tenkz-grid.code.tex` |
| `free` | `atom`, `join`, `region` | `tenkz-free.code.tex` |
| `lattice` | `lattice`, `site`, `region`, `edge`, `cup`, `trace`, `pairtrace`, `label-anchor-site`, `surface`, `boundary` | `tenkz-lattice.code.tex` |
| `cd` | `cdcell`, `cdobject`, `cdmap`, `cdarrow`, `tree` | `tenkz-cd.code.tex` |

Notes against the previous table: grid never emits `leg` or `fuse`; a
deferred range decoration emits `span` with its row, column, length, and
kind.  `\tnput`'s event kind is literally `atom` (with a `kind=` attribute selecting its inkless-endpoint
skin), not `put`; `lattice` was previously undocumented entirely, and its
`tenkzplanes` pictures do emit a `boundary` line (contradicting a stale
`ch-reference.tex` sidenote that has been corrected alongside this table).
The lattice-only `surface|picture=N|name=tenkzplanes` event records execution
of that public preset while the enclosing picture remains `lang=lattice`; it
is model-owner metadata, not a second picture language.
`scripts/tenkz_audit.py`'s `DIALECT_KINDS` is generated from this same
grep and must be kept in step with it by hand until a script does the
generation.

**The `at=rows` emit/input asymmetry.** `physical=rows` is an *input*
token (`tenkz_normalize_physical_face:Nn`, `tenkz-grid.code.tex`) meaning
"ports span the whole row's width, not this cell's face." On the *emit*
side, `\tenkz_emit_faceports_rows:nnn` writes the literal string `at=rows`
as a `faceports` event's `at=` value — a sentinel meaning "no per-cell
slot list was computed; consult the row," not a resolved position list
the way `at=` reads for every other `faceports` event. A `.tnlog` consumer
must special-case `at=rows` as non-positional. See the one-line note at
the emitter (`tenkz-grid.code.tex`, `\tenkz_emit_faceports_rows:nnn`).

`\tndefine`/use emit `def|name|hash` / `use|name`. plasTeX compiles
bodies standalone, so identical events flow in web builds.

### 5.2 The sugar contract (G21)

`sandwich`, `physical=`, `\tnX`, `\tntree`, and every builder expand to primitives producing **byte-identical event streams** to the manual spelling. This is a documented, CI-tested contract: the audit cannot distinguish sugared from hand-composed figures, and deferred decorations address the same named cells either way.

### 5.3 Type checks

Structural in the grid: bonds are virtual–virtual and pairings physical–physical **by construction** — mismatches are inexpressible, so checks move from runtime to parser. Runtime assertions fire exactly where free composition exists: `\tnjoin` in `tenkzfree`. The `morphism` port type is deleted; `cdmap` and `cdarrow` are their own event species and never enter the contraction graph.

### 5.4 Invariants

*Hard errors (compile time):* leg-parity violations in paired rows; unequal column counts (cell-coordinate error message); out-of-range spans; unknown span modes; lattice cell sets outside grid bounds; unresolved or duplicate enclosure names; polygon arrows to nonexistent vertices; duplicate `\tndefine`; port-type mismatch in `\tnjoin`.

*Hard errors (audit time):* malformed region records (lattice regions require `cells=`, free regions require `members=`); duplicate free enclosure names; a free region member not declared by an earlier atom, named join, or named region; empty picture — any `lang=grid|lattice|free` picture with zero content events (would have caught all 33 fake diagrams); a `figure`-wrapped picture whose body emitted no events (caption-mismatch class).

*Advisories (never build failures):*
- **Ellipsis policy:** a `periodic` chain of ≥ 4 columns without `\tndots`.
- **Repeated topology:** canonical label-inclusive graph hash per picture; isomorphic bodies across chapters reported as `\tndefine` candidates.
- **Role stability (G10):** region slots clustered by resolved cell set per chapter; "`selected` bound to R in fig 3 but T in fig 5" is flagged.
- **Transfer-map canonicality (G11):** pictures isomorphic to the canonical transfer map drawn without `sandwich` are flagged as probable drift.
- **Cache honesty:** stale/orphaned SVGs listed against per-picture source hashes.

### 5.5 Cross-engine and externalization policy (G12, G13)

CI compares the **multiset of canonical graph hashes** between the xelatex print build and the xdv→dvisvgm web build — print/web identity checked semantically, not just at pixel level. Externalization: a flag event is written at `\begin{document}`; the audit refuses logs produced with externalization enabled; CI owns the authoritative `.tnlog`; author builds may externalize freely.

### 5.6 Migration gates (G9)

Per migrated entry: (a) pixel diff against the old render, with intentional changes whitelisted from the 221-defect fix list; (b) event-graph isomorphism of the typed contraction graph, waivable per figure with a one-line justification in the PR (same discipline as paper-gap notes).

### 5.7 Lint and corpus layers (G15, G17)

`tenkz_lint.py` bans literal `...`/`\ldots` inside picture bodies (use
`\tndots`) and rejects raw off-theme ink in native environments; the escape is
`% tn-lint: allow ⟨rule⟩ ⟨reason⟩`. The adopted corpus under `tests/tenkz/`
compiles and audits through `scripts/tenkz_corpus.sh`, with optional 200-dpi
render baselines for visual review. Focused regressions cover web capture,
equation layout, labels, face ports, enclosures, torus closure, index routing,
and tree topology. This maintained corpus replaces the proposed generated
chapter-page and perceptual-hash pipeline.

### 5.8 Deleted from the audit

Contexts/role/profile hand-entered metadata and their assert-equal churn (now derived); the chapter-local-TikZ ban; the repeated-topology-must-be-motif failure and its motif-exemption loophole; the unused-diagram and PEPS-chapter-usage checks.

### 5.9 Key-surface census (2026-07 gate)

143 leaf `/tenkz` pgfkeys, across 14 families — counted by collecting direct
`.code`, `.store~in`, and `.is~choice` leaf declarations and expanding every
`\tenkz_install_core_forwards:nn` call in `tex/tenkz/*.code.tex`; choice-value
branches, family roots, and `.unknown` handlers are excluded:

| Family | Leaf keys | Source |
|---|---:|---|
| `/tenkz` (root) | 5 | `tenkz-core.code.tex` |
| `/tenkz/grid` | 23 | `tenkz-grid.code.tex` |
| `/tenkz/cell` | 23 | `tenkz-grid.code.tex` |
| `/tenkz/span` | 4 | `tenkz-grid.code.tex` |
| `/tenkz/lattice` | 28 | `tenkz-lattice.code.tex` |
| `/tenkz/region` | 7 | `tenkz-lattice.code.tex` |
| `/tenkz/edge` | 5 | `tenkz-lattice.code.tex` |
| `/tenkz/site` | 3 | `tenkz-lattice.code.tex` |
| `/tenkz/put` | 10 | `tenkz-free.code.tex` |
| `/tenkz/join` | 9 | `tenkz-free.code.tex` |
| `/tenkz/free region` | 7 | `tenkz-free.code.tex` |
| `/tenkz/cd` | 8 | `tenkz-cd.code.tex` |
| `/tenkz/tree` | 6 | `tenkz-cd.code.tex` |
| `/tenkz/arrow` | 5 | `tenkz-cd.code.tex` |
| **total** | **143** | |

For scale, quantikz's public key surface is roughly 40 — tenkz is a wider language by design (four sub-languages, not one), but the ratio is worth carrying forward rather than re-discovering at the next gate. No family here is flagged for removal: this is a measurement, not a verdict. Pruning candidates (a family whose keys have exactly one call site across `tex/tenkz/examples/` and the blueprint chapters) are **0.9-freeze material** — the manual and reference chapter become the binding contract at 0.9 (GOAL.md), and a key still resting on a single call site at that point is the moment to cut it, not before. Record the count at every gate (issue #4158); prune later.

---

## 6. Completed migration — 114 catalogue entries, 140 call sites

Every former call site now contains a native body or exact mathematics. The
33 equation-only wrappers became displayed formulas; regular contractions use
the grid language; fusion and map diagrams use `tenkzcd`; regions and sheets
use `tenkzlattice`; irregular graphs use `tenkzfree`. The non-PEPS batch left
13 declarations serving 15 PEPS calls, and the PEPS batch reduced both counts
to zero.

The exact demolition base contained seven obsolete TeX files (2,353 lines)
and four registry-pipeline files (2,831 lines), plus a separate two-line web
template. They were unused after the chapter migration and were removed with
their build paths and workflow hooks. `MIGRATION-MAP.md` retains the complete
entry-by-entry disposition; `DEMOLITION.md` records the exact final census and
persistent literal-zero gates.

The migration gates were source comparison, formula and ink-to-index comments,
typed contraction and boundary accounting, event audit, and visual print/web
inspection. Pixel resemblance to the retired rendering was never sufficient
when the cited mathematics required different topology.

---

## 7. Documentation — the second-edition manual

`docs/tenkz/manual2.tex` is the quantikz-style citable artifact. Its examples
compile in CI, while the larger adopted corpus supplies repository-wide audit
and render coverage.

1. **Install & ship** (½ page): two-line usage; arXiv shipping list; engine notes (xelatex; dvisvgm for SVG).
2. **Tutorial** (5–6 pages): spine is literally B1→B8, one concept per boxed example, rendered output beside verbatim source; includes the **deliberate type-error demonstration** (G24: a physical–virtual `\tnjoin` and the compile error it produces).
3. **Reference** (~2 pages of tables + one block per command): per environment a key table; per command one signature line, key table, minimal example, and the printed **"why this is a command and not a key"** justification (G22) — the anti-sugar-creep rule is part of the citable contract.
4. **The house style** (2–3 pages): glyph dictionary (glyph, key, mathematical meaning); semantic hue table and region slots; the metric table in geometry-appendix format (G23: constant, value, derivation from pitch, printed motivation); ellipsis and label-quadrant policies; the **canonical-spelling table** — one sanctioned drawing per semantic object (transfer map: sandwich vs opaque pill, and when each is correct); the **genre-ownership table** (G23) mapping every Tier-A/B/C use case in the brief to exactly one sub-language home.
5. **Sub-language chapters:** tenkzcd (grid mode, polygon mode, the raw tikz-cd fallback shown side-by-side per G25, `\tntree` grammar including internal charges and module-tree marks); tenkzlattice (cell-set algebra, semantic roles, side policies, and stacked-sheet closures); tenkzfree (typed anchors, `\tnjoin`, and the escape policy: when free placement is legitimate).
6. **Extension:** worked `\tndeclareatom` example (adding the RMP circle-matrix-on-wire glyph) documenting the typed-port contract; restyling via `\tnset` with the complete style-name table.
7. **Migration record:** `MIGRATION-MAP.md` preserves the original census,
   entry dispositions, and idiom conversions without exposing a second API.
8. **Troubleshooting:** real failure modes with cell-coordinate error messages
   (missing `{}`, trailing `\\`, unequal column counts, `&` under plasTeX and
   `align`), top-level equation siblings as the **&-free fallback**,
   externalization-vs-audit interaction, and stale SVG cache.
9. **Regression suite:** B1–B8, standalone examples, and the adopted corpus;
   `scripts/tenkz_corpus.sh --render` produces the visual-review baseline.
10. **Citation** (CITATION.cff + BibTeX; manual versioned with the package).

Repository guidance lives in `docs/blueprint_style_guide.md` and
`docs/tenkz/HACKING.md`. All chapter-facing names obey `docs/prose_style.md` —
keys are `periodic`, `sandwich`, `conjugate`, `fused`, never software jargon.

---

## 8. Questions considered during design

1. **Hull-tracer escalation.** Should a stalled notched-outline tracer gain a
   preprocessing helper, or should `outline` remain restricted to
   simply-connected sets with `fill` mode for notched figures?
2. **Repeated names.** Should the roughly dozen multi-use figures remain as
   parameterized house spellings, or should full inlining leave only the
   canonical-spelling table as shared reference?
3. **Slides scope.** Should the dark-theme slide deck migrate with the package,
   or should slide rendering remain a follow-up?
4. **Inline-atom accessibility.** Should the web renderer turn an entire equation containing `\tnpic[inline]` into one SVG, or should source mark display-adjacent diagram rows explicitly so operator text remains selectable?
5. **Publication.** Should tenkz ship as a standalone citable package at
   migration completion, or remain repository-internal for one release cycle?
---

## 9. Final outcomes (updated after migration)

The final outcomes are:

1. **Hull tracer**: pure expl3 rectilinear tracer with notches, no Python in the TeX path; if it
   stalls, `outline` restricts to simply-connected sets (fill mode covers notched figures).
2. **The named dozen**: fully inlined; no catalogue-like house layer remains.
3. **Slides**: migrated to the native package during catalogue demolition.
4. **Inline-atom accessibility**: explicit `tenkzequation` rows are the web contract. Each diagram
   atom is an SVG with source-derived alternative text, while the operators between atoms remain
   selectable; true running-text atoms stay an ordinary-TeX capability.
5. **Publication**: repo-internal for one release cycle, then CTAN/arXiv.

## 10. Additional hard requirements (maintainer, 2026-07-16)

- **Labels must not overlap diagram ink by default.** Every label site is a reserved band derived
  from the metric system (leg-tip band, bond-midpoint band, free-quadrant of a bead, brace band);
  automatic placement (`pos=auto`) derives the quadrant from the atom's occupied sides. Every
  label accepts `label pos=` (compass override) and `label shift={dx,dy}` (nudge). Collisions are
  design bugs, not user errors.
- **Tutorial must include a worked-examples chapter of complicated MPO/PEPS figures**: expectation
  -value windows, MPO-MPO products, zipper/pulling-through, fusion trees and the pentagon, MPDO
  purification, PEPS windows with notched regions, torus geometry — each shown as rendered output
  beside verbatim source.
- **Rendered review artifacts must be tightly cropped**: per-figure standalone-class pages
  (border ≤ 6pt), never fixed large pages with centered figures.
- **Coverage matrix**: the manual ships a table mapping every figure genre of arXiv:2011.12127
  (RMP) and arXiv:2203.12563 to its tenkz spelling (or names the planned extension), so coverage
  is checkable rather than aspirational.

## 11. Tensor-style modes (added 2026-07-16, maintainer request)

The glyph policy is declarative: `\tnset{tensor style=dot|box}` (document-wide) or the same key
per picture. `dot` (default) renders unadorned `\tn{A}` as a CPSV-school bead with the label
placed outside by the auto-quadrant algorithm; `box` renders it as a box with the label (or
`\overline{label}` for `\tn*`) typeset inside, suppresses external auto labels, and tightens
brace clearances (the clearance keys off whether external dot labels actually exist in the
spanned columns). Explicit per-cell skins always override the policy; the event stream records
the resolved skin. All inscribed glyphs carry a uniform-height strut so boxes labelled `A`,
`T_g`, `A^{(2)}` sit at one height (small multiples must be uniform).

---

# Phase 0.5 — the mathematical-soundness overhaul (recorded 2026-07-17)

> **Pre-0.6 record.** Sections 12–17 record the Phase-0.5 design in its
> 0.5 spellings, written before the 0.6 rename sweep. The shipped grammar
> renames: `close west`/`close east` → `west=cup`/`east={cup=$m$}` (§13);
> `pair=trace` and `trace={physical at=…}` → the one cell-set grammar
> `trace={(interface, cols)}` (§14); `plane=` → `frame=` (§15.2);
> `orientation=vertical` → `frame=vertical`, and `periodic style=` →
> `periodic, trace style=` with the policy side effect removed (§15.5).
> See `CHANGES-0.6.md` for the surviving surface.

A five-lane mathematical audit of the Phase-0 package — every manual diagram, the school's
drawing conventions, twelve hard figures from the CPSV RMP (arXiv:2011.12127), eight hard
constructions from arXiv:2203.12563, and the pentagon — found one systemic defect and a ranked
list of missing primitives. Phase 0.5 is the correction. The sections below record what was
decided and why; each decision was accepted only after a declarative reproduction of the
published figure it serves.

The yardstick for every addition is a standing maintainer directive: a new feature must
collapse existing special cases into one concept, never add another case. Three unifications
carry the phase — the frame (§15), the side policy (§12.3), and the column contraction policy
(§14). Where an old spelling survives, it survives as a documented one-line alias of the
unified grammar, not as a parallel mechanism.

## 12. The boundary doctrine

### 12.1 Open is the default; no open legs means a scalar

An open virtual index is data. A row's virtual wire that reaches the row's extremal occupied
cell and is not closed by a trace, a cup, or a fusion bar protrudes as a stub of length
`virtual stub` = 0.45·pitch, drawn in the row's wire style. The ink states "matrix-valued on
this side"; sealed ends state "boundary-contracted on this side"; a picture with no open legs
of any kind denotes a number.

**Default: `boundary=open`.** `\begin{tenkz} \tn{A} & \tn{B} \end{tenkz}` denotes the matrix
product AB — one open virtual index west, one east. The grounds, in order of force: (a) under
the sealed Phase-0 default, 9 of the 14 benchmark/stress figures and nine manual diagrams were
mathematically false — every matrix- or operator-valued object rendered as a vector or scalar,
the transfer map worst of all (a superoperator drawn with zero of its four legs); (b) the
school draws protruding ends everywhere and closes them only with explicit ink — a loop, a
cap, or a boundary tensor; "sealed" is never a default in the literature; (c) sealing is the
rarer intent, so it is the one that must be spelled: `boundary=none` is the author's assertion
that boundary vectors are absorbed. A default that silently misstates rank fails the package's
own type discipline.

### 12.2 Boundary signatures and equation well-formedness

Every picture emits a boundary-signature event:
`boundary|picture|virtual-west|virtual-east|fused-west|fused-east|physical-up|physical-down`.
Closures — traces, cups, boundary-vector glyphs — count zero; a fusion bar's combined leg
counts one fused open index on its side. A diagrammatic equation is well-formed iff both sides
expose identical signatures. This is the doctrine that caught B8's double-counted physical sum
and hard11's spurious input stubs; the audit layer lints it: pictures sharing an `eq=<tag>`
must match exactly (hard error), pictures emitted from the same source line are compared as an
advisory (display math legitimately mixes pictures with scalars).

### 12.3 The side policy

A picture side (west or east) has exactly one policy: **open** (stubs) | **none** (sealed) |
**trace** (row to itself — `periodic`) | **cup** (row to row — §13) | **consumed** (a glyph
owns it: a fusion bar, a source bead). The grammar presents this as one choice per side rather
than as interacting keys; `boundary=` is the both-sides shorthand and `periodic` the
row-to-self form. Resolution is local-wins: cell > row > side > picture.

- Picture: `boundary=open|none|periodic`; per-side `west=open|none`, `east=open|none`.
  Prepared or discarded indices are properties of a *side* of the word, not of a row — a
  circuit fragment seals its west inputs while its east outputs stay open (the hard11
  brick-circuit blocker, closed by exactly this key).
- Row: the colon-mod grammar `rows={op:open, ket:none, wire:fused, …}`; mods combine in any
  order.
- Cell: `left=<math>` / `right=<math>` label the stub tip and imply the stub; `no left` /
  `no right` seal one end of one row. Tip labels are legal only on the row's extremal occupied
  cell; elsewhere they are a compile error with cell coordinates.
- `\tndots` at a row's end draws no stub and counts zero: the ellipsis states continuation,
  not openness. Terminal `\tnghost` cells are excluded from row extent, and the ghost-padding
  workaround idiom draws a lint advisory — the boundary model is the spelling.

### 12.4 The trace-clearance correction

The first table fixed `trace clearance` at 0.55·pitch, while the early source
used 0.62. Both constants predicted the outer row's ink and both failed when a
different glyph or label changed that ink. An intermediate additive budget
made the dependencies visible but still duplicated the drawing passes' model.
The final rule measures instead:

    trace ordinate = row axis ± (measured silhouette + daylight)

The silhouette includes the rendered glyph edge, each facing physical leg and
label band, pair-trace cap, external bead label, and fusion overhang. The sole
added distance is `daylight = 0.15·pitch`, pure separation beyond the measured
ink. There is no trace-clearance ratio to retune and no consumer predicts what
another pass draws.

## 13. Cups and the canonical channel spellings

(0.5 spelled the cups `close west` / `close east`; 0.6 renamed them to
`west=cup` / `east={cup=$m$}`, see CHANGES-0.6.md. The record below
keeps the 0.5 spellings.)

`close west` / `close east` are picture keys: on that side, adjacent open wire rows are tied
to each other in pairs, top-down (rows 1–2, 3–4, …), each pair by one smooth 180-degree bend.
A cup contracts two *different* rows' indices; `periodic` contracts a row with itself — the
two closures are distinct topologies and distinct ink. A bare value gives the plain cup (an
isometry contraction); `close west={$\rho^R$}` seats a boundary glyph on the bend — a
tensor-style dot on the arc apex, label placed outward. Cupped sides draw no stubs and count
zero in the signature.

The channel spellings are canonical and the manual states them as law:

| Object | Spelling | Signature (vw, ve, up, down) |
|---|---|---|
| the map E_A | `[sandwich]`, all four virtual stubs open | (2, 2, 0, 0) |
| the value E_A(X) | `[sandwich, close west={$X$}]`, east pair open | (0, 2, 0, 0) |
| the n-site density matrix | `rows={ket:nopair, bra}, close west={$\rho^R$}, close east={$\rho^L$}` | (0, 0, n, n) |

Naming the map draws it fully open; applying it closes the input side with the argument
riding the cup; closing everything denotes the scalar. The density-matrix racetrack composes
under `\left(…\right)` on the wire axis, so eigenvalue equations wrap it with no glue. One
corollary of the signature doctrine, fixed in B8: inside `\sum_i`, the summand
X ↦ A^i X A^{i†} is drawn as `rows={wire,wire}` with *no* vertical wire — the index i is fixed
by the outer sum, and drawing the physical contraction would count it twice.

## 14. The marginal contraction policy

(0.6 replaced `pair=trace` and `trace=physical at={…}` by the one
cell-set grammar `trace={(physical, c-c)}` / `open={(i,c)}`, see
CHANGES-0.6.md. The record below keeps the 0.5 spellings.)

Between two physically-facing layers, each column takes exactly one of three values: **pair**
(the straight contracted leg — the default), **open** (both legs dangle — the indices you
keep), or **trace** (a wrap loop around the column's east side, from the ket's up leg past
both rows into the bra's down leg — Tr over that site's physical space). This is the whole
grammar of marginals: rho_kept = Tr_traced |psi⟩⟨psi| is drawn as `rows={ket:nopair, bra}`
with `trace` at the discarded columns — open pairs on the kept sites, loops on the traced
ones. A traced column contributes nothing to the signature; a kept column contributes up+down.

Spellings: the per-cell key `pair=trace` and the picture sugar `trace=physical at={4,5}` in
the grid; the cell-set keys `open={(r,c),…}` and `trace={(r,c),…}` in `tenkzplanes`, where the
loop is drawn in the paper frame, east-routed around the site column. The acceptance figure is
RMP Fig. 2 in both panels: (a) the MPS marginal — three open pairs, two loops; (b) the PEPS
double layer with the rightmost column traced sheet-to-sheet.

The ladder rule applies: one vocabulary — `contract=pair|open|trace` at cell, column, row, and
picture scope with uniform cell-set addressing — serves grid and planes identically. The
spellings above are its aliases, one table row each.

## 15. The frame

### 15.1 One linear map

Every geometry request of the phase — oblique PEPS sheets, mirror lean, the depth axis,
vertical chains — is one linear map L from logical (col, row) to paper (x, y):

| Frame | L |
|---|---|
| flat | [[lp, 0], [0, −lp]] |
| oblique | [[lp, −slant·lp], [0, −rise·lp]] |
| lean=west | negate the slant column |
| vertical | [[0, −lp], [lp, 0]] |

Presets are the interface; the matrix is the mechanism. The region tracer commutes with any
linear L (intersect-then-map = map-then-intersect, proved in the mirror probe), so hulls,
margins, fills, and corner labels survive every frame without special cases.

### 15.2 Plane presets

(0.6 renamed `plane=` to `frame=`, see CHANGES-0.6.md.)

Three values of `plane=`, each a documented read, plus two guarded escape hatches:

- `plane=flat` — the Phase-0 rectilinear grid. Unchanged.
- `plane=oblique` — the default, slant 0.45 / rise 0.60. Rise must exceed
  physleg/latticepitch = 0.38/0.75 ≈ 0.507 or physical legs collide with the behind-row bond;
  the old 0.55 left leg tips 0.043·lp short of that bond — a near-touch that merges at compact
  pitch. 0.60 clears the threshold by 0.093·lp and keeps the flat-sheet foreshortening that
  higher rises lose.
- `plane=slab` — slant 0.60 / rise 0.55, the full-pitch RMP showcase geometry (47-degree
  leg/bond separation, best lateral clearance). Named for the read, not the numbers; it costs
  1.8·lp of drift over four rows, which is why it is a preset and not the default.
- `plane slant=` / `plane rise=` — explicit per-picture ratio overrides. Guarded, not clamped:
  the log warns when rise ≤ physleg/latticepitch (the leg-crossing regime) and when slant
  leaves (0.30, 0.65) (below, depth bonds become confusable with vertical legs; the 0.30/0.70
  cell is the proven worst case).

A rise-0.70 "steep" preset was rejected: its one advantage is substantially captured by the
0.60 default, and a third oblique preset is option soup — `plane rise=0.70` is one key away.

### 15.3 Lean; the depth axis

`plane lean=east|west` (default east, the "/" lean) mirrors the sheet by a sign flip on the
slant register; the frame map is linear, so the tracer, fills, margins, and labels survive
unchanged. Compass naming matches the library's west/east vocabulary; `lean=mirror` was
rejected for naming the mechanism instead of the result.

Swapping the depth axis (columns receding) is not supported. The 5×3 probe is decisive: the
window silhouette collapses toward a rhombus staircase (drift/width ≈ 0.9) and the depth reads
as a rotated lattice. The manual states the stance; a tall-window guard warns when
(rows−1)·slant > 0.5·(cols−1), with the documented remedies (cap receding rows near four at
stock slant, or drop slant toward 0.30 beyond that).

### 15.4 Sheets

The static sheet separation is dead. `tenkzplanes` derives its default:

    sheet sep = (rows − 1) · planerise + planegap,        planegap = 0.70

`planegap` is a named ratio: the air between fully disjoint sheets, matched to the RMP
double-layer panel. No static number survives a row-count change — the old 1.4 crowded the
3×3 workhorse and interleaved outright at four rows. `sheet sep=` remains as a total-offset
override, with a warning when a user-set value re-interleaves the sheets.

The double layer carries its own local slant/rise, 0.40 / 0.45: 0.40 is the unique slant
maximizing pairing-leg-to-dot clearance (0.2·lp for every leg climbing up to four row-levels;
the single-sheet 0.45 puts two-row legs inside the dot radius — a rim clip), and 0.45 gives
the squat RMP-like stack. Only the double layer has multi-row pairing legs, which is why the
two objects legitimately differ; the ratio comments record the reason per the metric doctrine.
The manual states the avoid band — never rise 0.48–0.52, where a stub tip sits ambiguously
tangent to the next row's bond — and the size ceilings: 3×3 is the workhorse, 4×4 the maximum
for any figure read cell-by-cell, 5×5 the absolute maximum for impression-only panels.

### 15.5 Vertical chains

(0.6 deleted `orientation=` in favour of `frame=vertical`, and split
`periodic style=` into `periodic` — the whether — plus `trace style=` —
the how, with the selection side effect removed; see CHANGES-0.6.md.
The record below keeps the 0.5 spellings and the side-effect-as-design
reading that 0.6 reversed.)

`orientation=vertical` (alias `chain axis=south`) rotates the whole grid grammar 90 degrees
through the frame map (x, y) → (−y, −x): columns descend the page, bonds run vertically,
physical legs point west/east by row type, `\tndots` renders `\vdots`, and the label
auto-quadrant rotates with the frame. The corpus contains exactly two rotated genres — the
vertical O_L MPO word with side-hook closure and the transfer-matrix column — and both are
pure 90-degree rotations of existing grid semantics; the free tier cannot carry them (its
label band is struck through by any south-going wire). Constructs the frame does not yet
transform warn and are skipped: silently wrong ink is the one forbidden outcome.

`periodic style=racetrack|hooks` selects the closure ink; setting it also selects periodic, so
the O_L word is one option list. `hooks` is the RMP O_L closure — at each end the wire runs
half a stub out and turns a near-semicircle toward the return side, each hook one path with
reach set by the stub ratio, so the rounding is uniform by construction. A vertical periodic
word closes with hooks by default; horizontal words keep the racetrack.
<!-- The per-frame default flip ships with the vertical polish; an explicit periodic style=
always wins. -->

Rejected: a general `rotate=` angle on `\tnpic` (only 90 degrees appears anywhere in the
corpus, and arbitrary angles rotate label baselines against the horizontal-text doctrine); a
`chain path` key for L-shaped chains (two `\tnjoin` calls already produce publication-grade
corners — the manual documents the idiom). The free tier gains the stopgap
`label pos=north|south|east|west` on `\tnput`.

Net grammar growth for the whole frame family: six keys, one named ratio (`planegap`), three
log warnings, zero removals.

## 16. Directionality

Arrow semantics follow the source study: an outgoing arrow is the vector space V, an incoming
arrow its dual V*; contraction joins out to in only; arrow reversal is the dual — the inverse
representation. Arrows survive rotation where positional reading order dies, which is why they
are bond data, not decoration.

Keys only, no new commands: row tokens `dir right` / `dir left` in the `rows=` suffix grammar
(three-valued — absent, right, left); the picture key `bond dir=right|left` as the default for
all wire rows, with the per-bond override `bond dir={right, left at 2/3-4}` — per-leg reversal
is mathematics (the inverse representation) and must be per-bond expressible. The mark is the
existing `bond arrow` style — a mid-wire barb at 0.55, inheriting the wire color — with a
`fused bond arrow` variant sized to span the doubled wire. In a periodic picture the barb
rides the racetrack return wire, the MPO ring convention. The free tier takes a `dir` key on
`\tnjoin`, argument order giving the direction.

The event stream carries it: bond events gain `dir=none|forward|reverse`, and the boundary
signature splits directed open legs (virtual-west-in/out) — oppositely-directed open legs are
unequal in equation comparison. Not dir's job: fusion chirality (that is `\tnfuse combined=`),
conjugation (that is `\tn*`), and reading order (a manual note, no ink). Physical-leg arrows
are roadmap; only the weak-Hopf paper needs them.

## 17. The gate process

Phase 0.5 ran under three standing gates, and the phase's own history is the argument for
them.

1. **The simplifier between phases.** A code-simplifier pass runs over every grown module
   between phases, under a pixel-identity regression gate: baseline renders first, byte-equal
   event streams and unchanged pages after. Two passes cleaned Phase 0; a third cleaned the
   grid, lattice, and cd modules after the Phase-0.5 growth.
   The durable render contract is the corpus-wide 200-dpi before/after procedure in
   `tests/tenkz/README.md`: issue #4158 requires equal fixture/page censuses and PNG checksums
   for behavior-preserving work, while intentional changes require page-by-page visual review.
2. **The mathematical referee.** Every figure is refereed against its formula: the formula is
   stated; the ink matches it exactly — open legs counted (no open legs = scalar), signatures
   balanced across `=`, the channel spelling canonical, conjugation on the bra layer, trace
   and cup topologically distinct; inline `%` comments must be mathematically true. The
   Phase-0.5 audit was the first full referee pass — five parallel lanes feeding one architect
   spec — and it is what found the sealed-boundary defect that Phase 0's visual gates missed:
   a diagram can be beautiful and false. Acceptance thereafter was reproduction: every missing
   primitive was named by a failed declarative reproduction of a published figure, and closed
   only when the re-attempt rendered faithfully with balanced signatures, verdicts recorded as
   clean, clean-with-noted-gap, or still-blocked.
3. **The prose gate.** Manual and documentation prose follows the Elements of Style: every
   sentence asserts. Hedges, caveats, and self-commentary go in `%` comments — sanctioned
   murmuring, visible in printed source blocks — never in the running text.

### 17.1 Recurring simplification gate (2026-07-20)

The gate asks three questions after each migration slice.

1. **What grew ad hoc?** The `tenkzlattice` public key family outgrew its
   reference table. The table omitted `pitch`, `compact`, `inline`, `tensor
   style`, `species`, the oblique-frame overrides, `sheet sep`, `pairing`,
   `open`, `trace`, and the three expert basis vectors; it also omitted
   `updown` from `physical`. The design still advertised the unimplemented
   `topology=`, `remove=`, and `site=\tnpic{…}` forms, while the edge and site
   signatures predated their real key families. The reference and
   quick-reference entries now describe the implemented surface.
2. **Which two things are secretly one thing?** Drawing, silhouette, and
   boundary-counting passes repeated the same question: does `(r,c,h)` survive
   both a whole-column removal and a sheet-addressed removal? They now share
   `\tenkzl_endpoint_exists:nnn`. Cup and trace routing remain separate: a cup
   joins the two sheets of one boundary port, whereas a trace joins opposing
   sides within each sheet.
3. **What would be deleted in a redesign?** `boundary legs` is exactly the
   compatibility spelling of `boundary=open`. Keep it while migrated sources
   use it; once an in-repository search reaches zero, delete the alias and its
   reference row rather than maintaining two names for one policy.

### 17.2 Recurring simplification gate (2026-07-22)

This run covered the native package and its manual after the catalogue
demolition.

1. **What grew ad hoc?** Documentation facts drifted from the mechanisms they
   described. The geometry appendix still printed a fixed trace clearance even
   though the renderer measures a silhouette and adds one daylight; it also
   claimed to transcribe every ratio while omitting most of the 38 named
   ratios. The web specification promised automatic whole-equation rerouting,
   while the shipped and tested contract is the explicit `tenkzequation` row.
   The appendix and web contract now state the implemented mechanisms.
2. **Which two things are secretly one thing?** The lattice and free-region
   commands expose one region grammar, but their parsing has different state
   effects and their renderers consume different geometry. Issue #4608 owns the
   shared declarative surface and its byte-identical event gate; this pass does
   not fold that medium-risk parser change into documentation repair. The six
   remaining implementation twins likewise stay in issue #4614 until each call
   site is audited. Similar slide bodies stay local: extracting whole figures
   would recreate the catalogue and remove the body that each slide may extend.
3. **What would be deleted in a redesign?** The following compatibility
   spellings remain part of the 0.6 transition surface. Counts are non-comment
   source lines at `a49dacc74` across examples, the adopted corpus, blueprint
   chapters, slides, and the manual.

   | Compatibility spelling | Canonical spelling | Lines | Files |
   |---|---|---:|---:|
   | `boundary legs` | `boundary=open` | 96 | 46 |
   | `label at=` | `label pos=` | 39 | 17 |
   | `route=curve` | `route=arc` | 70 | 25 |
   | `legs at=` | explicit face data | 27 | 17 |
   | `chain axis=` | `frame=` | 5 | 4 |
   | `boundary=periodic` | `west=trace, east=trace` | 2 | 1 |
   | `combined=` | explicit fused-face data | 48 | 28 |
   | `\tnfuse[rows=2]` | `\tnfuse[span=2]` | 1 | 1 |

   These spellings are kept because the manual does not become the binding
   contract until the 0.9 freeze. Before that freeze, rewrite every non-fixture
   client to the canonical form. Delete an alias only when that count reaches
   zero, removing its compatibility probe and manual row in the same change.


## 18. The silhouette (recorded 2026-07-18)

Every clearance question in a picture is the same question: how far does
the ink already there reach?  The **silhouette** is the answer, computed
once: `\tenkz_silhouette:nnnnN {row}{col-from}{col-to}{up|down} \dim`
returns the distance from a row's axis to the outermost ink edge over a
column span, on one side.  Closure and annotation ink then sits at

    silhouette + daylight

and nowhere in the package does a consumer predict what another pass
will draw.  A pass that adds a new kind of ink teaches the resolver
once; every consumer inherits the correction.

The resolver reads the same stored cell data the drawing passes read —
the kind, options, and node-name tables plus the row typing — and takes
a per-cell maximum over the actual contributions: the placed node's own
edge anchor (so strut-grown boxes, wide pills, `wires=k` covering
heights and the ellipsis node are measured, not modelled), an open leg
beyond that edge, a label band beyond a labelled leg tip, the
pair-trace wrap loop's cap, an external bead label whose resolved
quadrant faces the queried side, and a fusion bar's overhang.  Leg-tip
and bead labels share one band metric (`dotlabelband`), deliberately:
both are a name hung off ink.

### The one daylight constant

`\tenkz@r@daylight = 0.15` pitch is *pure separation*: the gap that
keeps a return wire or a brace from fusing visually with the ink it
skirts.  It clears nothing — what must be cleared is the silhouette's
business and is measured.  0.15 pitch is about 1.7 mm at the default
11 mm pitch (roughly 8.5 of the 0.55 pt wire widths) and still about
1 mm (roughly 5.3 wire widths) at the inline pitch.  It replaces the former
`traceclear = 0.30`, which budgeted a worst-case glyph inside a fixed
drop, and the braces' unnamed 0.20 offset.

### Converted consumers

- **The periodic racetrack** (`\tenkz_trace_row:nn`): drop = silhouette
  of the traced row's occupied span + daylight.  A bare ring hugs its
  beads; rings over labels clear the labels because the labels are in
  the silhouette, not because the racetrack guessed.
- **Span braces** (`\tenkz_draw_span:nnnnn`): offset = silhouette of
  the braced columns + daylight.  Braces measure over their own columns
  only, so a brace over unlabeled cells is not pushed out by labels
  elsewhere in the row, and a box-mode brace clears the *actual*
  (strut-grown) box edge instead of a nominal minimum.
- **Typed-map label bands** (`tenkzcd[maps]`): the uniform object-column
  gap is the widest opaque map-name band plus two daylights, with the
  historical map gap as its floor.  The actual label node is measured; no
  glyph budget or superscript allowance is predicted.

The former per-consumer scan functions `\tenkz_span_leg_labels:nnnnN`
and `\tenkz_span_dot_labels:nnnnN` are deleted; their logic lives
inside the resolver.

### Planned consumers

- **Cup reach**: today the cup bend protrudes exactly one `stub`, so
  open and cup-closed ends share a silhouette by decree.  Converting
  means asking the side silhouette (the west/east analogue over a row
  pair: stub tips, boundary labels) and bending at silhouette +
  daylight, so a cup around labelled boundary stubs clears the labels.
- **Lattice sheet separation**: the inter-sheet gap becomes the lower
  sheet's up-silhouette plus the upper sheet's down-silhouette plus
  daylight, replacing the fixed sheet-separation ratio that must today
  be tuned against the tallest decorated sheet.
- **Region insets**: a region outline's margin becomes the enclosed
  cells' silhouette toward each edge plus daylight, so outlines hug
  bare beads and step out around legs and labels instead of carrying
  one worst-case margin.

## 19. Named coefficient routing (recorded 2026-07-19)

Several coefficient tensors may depend on the same direct-sum labels without
turning those labels into one fused wire.  The free tier records this as an
explicit typed graph: each coefficient glyph declares one port per incident
index, each junction is a dot atom, and each labelled rail is a chain of
`\tnjoin` edges.  Sharing a glyph therefore never collapses two names into one
unlabelled strand.  This is the native spelling of the $j,q$ routing in
`II_RFP.png` from arXiv:1606.00608.

No routing command is added.  `\tnput` and `\tnjoin` already form the required
grammatical class, and a dedicated command would only abbreviate one graph.
The `boundary` skin of `\tnput` places an inkless typed endpoint, so open rails
and their labels enter the event graph without acquiring a spurious tensor
dot.  A regression should compare the complete join set and the degree of
every coefficient, junction, and boundary node.
