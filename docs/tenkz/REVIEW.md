# TNLean Tensor-Network TikZ Library — Deep Review & Redesign Tournament

*2026-07-16. Inputs: 9-agent source review of `tex/tn/` (5,970 lines TeX + ~2,800 lines Python),
257-page rendered-gallery visual critique (221 defects), figure-vocabulary extraction from
arXiv:2011.12127 (66 figures viewed), arXiv:1804.04964 (214 inline diagrams), arXiv:2203.12563
(122 inline diagrams), a quantikz interface study, and a 4-design/3-judge tournament.
Full reports: `wjchk4rdv.output` (source), `wyia43kx7.output` (visual), `ww2oephm5.output`
(benchmarks), `final_spec.md` (consolidated spec) — all under the session scratchpad/tasks dirs.*

---

## 1. Verdict on the current library

**The core calculus is genuinely good; everything above it institutionalizes the failure you
sensed.** No published TN paper or package has typed ports, a semantic audit, or layout profiles —
the bottom layer is ahead of the community. But the interface inverts its own design:

### The catalogue is a museum, not an interface
- 114 declared diagrams: **102 called exactly once, 92 zero-argument, theorem-named.**
- **34 contain no drawing at all** — bare `\ensuremath` formulas routed through the SVG renderer,
  several inside `\begin{figure}` with captions describing drawings that do not exist.
- The plasTeX web renderer can *only* render catalogue macros — chapter-local composition is
  structurally impossible. Every new figure costs 2–6 file touches (motif + catalogue entry
  repeating the name 7 times + chapter call).
- Consequence measured in the blueprint: the most geometric chapters (ch11 FT proof, ch22
  periodic ~2,632 lines, ch24 torus/region-transfer ~2,100 lines) have **zero diagrams**, while
  the transfer map is drawn **three inconsistent ways** across ch02/ch14/ch16. The interface tax
  suppresses exactly the ink the mathematics needs.

### Three grammars are fused into one (your "pentagon" instinct, confirmed and quantified)
- ≥ 11 call sites are **commutative diagrams** (fusion pentagons, F-move pairs, channel-map
  chains, proof storyboards). The pentagon is implemented as **5 single-use tree macros with
  labels a…j frozen into the code**, hand-laid at 3cm/4cm literals, arrows attached to raw
  internal anchors — and the same pentagon is hand-laid a *second* time with different metrics in
  the catalogue. `morphism` as a port *type* is a category error (arrows are not indices) and
  pollutes the contraction-graph audit.
- 9–10 figures are **lattice-region schematics** (PEPS R/S/T, collars, complements) whose actual
  data is (grid, cell subset, label), hand-traced as absolute-cm polygons in 7 one-shot macros;
  "selected" color means a different set in every figure.
- 5 more are channel/correlator figures misfiled in the PEPS motif file (the file header admits it).

### Special-case explosion (the Torvalds failure)
- Trivalent map: **22 macros for 1 primitive** (orientation × chirality × physical-variant as
  names, not keys). v/p/m × route: **~38 macros for 3 parametric families.**
- A parallel `Slide*` interface duplicates chapter diagrams and has already drifted
  (SlideTNTransferMap ≠ TNTransferMap).
- The atom registry is hand-synced metadata, already wrong (TNCompactTraceCell declared portless
  but composed via its InsertionW port).
- Layout profiles: 40 literals ≈ 14 independent choices + one 0.8 scale factor; **92–273 numeric
  literals inside motif bodies bypass the profiles entirely** (the compact profile silently fails
  for three-site chains, PEPS grids, most label offsets).

### The audit aims at the wrong invariants
- role/profile/contexts metadata are derivable, hand-entered, and asserted equal — pure churn; a
  *second use* of a diagram is a build failure until the central file is edited.
- `assert_repeated_topologies_are_motifs` forces centralization yet any motif event exempts the
  picture — it enforces annotation, not deduplication.
- **No check notices that a "diagram" is empty** or that a caption mismatches its content.
- Print (xelatex + unicode-math), web SVG (first engine found, no unicode-math), gallery
  (lualatex): three engines, so print/web identity holds only at source level.
- Bottom line: ~8,800 lines of infrastructure serve 140 figure calls — **~63 lines of machinery
  per placed figure**.

## 2. Visual critique (all 257 gallery pages)

**221 defects: 70 high, 101 medium, 50 low.** Recurring classes (these are what a redesign must
prevent *by construction*):

- **Legibility floor violations**: junction glyph is 0.4mm at publication size (invisible);
  insertion ring's dashed micro-outline renders as a fuzzy bead; PEPS-site physical leg sits ~2px
  from the North virtual leg and reads as an accidental double stroke.
- **Label anchoring wanders** quadrants across the site family (SW/SE/NW with no convention);
  floating labels with no attachment cue (TNCompactTraceCell has three).
- **Pentagons**: label–wire collisions (F_i^{bcd} over the cd legs, j on an arrow path), a
  visibly skewed leg, F-arrows indistinguishable in weight from tree edges, not pentagon-shaped.
- **Ellipsis inconsistency**: some periodic chains omit ellipsis entirely while labels imply
  omitted sites; top/bottom rails place dots at different heights.
- **Equation rows** where `=` does not optically align with the wire axis.
- **Dark theme reshapes** (open ring → filled disc), erasing the insertion-vs-tensor distinction.
- Worst offenders: TNMPDOFusionTracePower, both pentagons, TNPEPSBlockedMiddleLocalGaugeFormula,
  TNMPV/TNMPVOverlap, the Slide* deck (label collisions, struck-through captions).

## 3. What the benchmarks taught us

- **RMP 2011.12127**: 91 includegraphics vs 14 figure environments — diagrams are *terms in
  equations*, glued by `=`, sums, stretchy delimiters. Full glyph dictionary extracted (beads,
  boxes, pills, canonical-form triangles, circle-matrices, parallelogram MPO tensors, 5-hue
  semantic color system, four distinct arrow roles).
- **1804.04964 (normal PEPS)**: all 214 diagrams inline TikZ; needs trace-box as first-class
  boundary, bond insertion as a *decoration on a named bond*, region overlays computed from site
  sets (the single-site notch is the mathematical crux and must be legible), and this school is
  **undirected and arrow-free**.
- **2203.12563 (MPO symmetries)**: 122 inline tikzpictures from 12 parameterized pics with named
  anchors — proof that anchor-chaining composition works; demands fusion trees with chirality,
  module trees, zipper equations with n-site braces, lasso scalar diagrams, diagrams inside
  `\oplus/\otimes/pmatrix`.
- **quantikz**: the interface gold standard — expl3 body capture over pgf-matrix, implicit wiring,
  content-addressed cells, uniform key-value options, documented style table, ghost cells,
  align-equals-at, total TikZ escape hatch, tutorial-first citable manual.

## 4. The tournament

Four independent designs, three judges (chapter-author lens, Tufte lens, maintainer lens):

| Design | Philosophy | Total (3 judges × 70) |
|---|---|---|
| **tenkz** — "the equation is the diagram" (quantikz-maximalist grid) | **179 — winner (2/3 judges)** |
| Quartet — four small languages, one style system | 176 (judge-author's pick) |
| tncalc — typed port-graph calculus perfected | 156 |
| tnplain — burn the framework, <800-line vocabulary | 145 |

The judges split honestly: the author-judge preferred Quartet's explicit sub-language boundaries;
Tufte and maintainer judges preferred tenkz's defect-prevention-by-construction and call-site
economics. The synthesis takes tenkz and grafts Quartet's five distinguishing assets (slice
contract, typed rows, event-graph iso migration gate, role-stability audit, genre-ownership
table) plus one-off wins from tncalc and tnplain — 26 grafts total, all recorded in the spec.

## 5. The consolidated spec (see `tenkz_final_spec.md`)

Headline decisions:

- **Package `tenkz`**, 4 environments + 17 commands + ~45 keys, CI-capped API surface.
  Sub-languages: `tenkz` (contraction grid: rows = layers, columns = sites, implicit bonds),
  `tenkzcd` (commutative diagrams: tikz-cd pass-through + `polygon=5` mode + `\tntree` fusion
  trees from bracketing words `(((a\,b)_x c)_y d)_e`), `tenkzlattice` (regions as cell-set
  algebra: `{R - (2,2)}` computes the notched hull), `tenkzfree` (typed-anchor free placement,
  the only place runtime port assertions remain).
- **A 3-site periodic MPS word is one body line**; the transfer map is 2 lines with `sandwich`;
  no registration, no catalogue, no figure wrapper. `\tnpic{...}` is the bridge: an inline math
  atom usable in running math, as a cd object, or as a lattice site skin.
- **`morphism` port type deleted**; arrows live in tenkzcd with their own event species.
- **Metrics**: one 11mm pitch + 8 documented ratios (each printed with its motivation);
  profiles are a scale factor and *cannot* be bypassed by literals. Every visual-critique defect
  class is closed at the style/shape layer (junction ≥ 0.9mm, solid insertion ring, `pos=auto`
  label quadrants, dark theme recolors-never-reshapes, `\tndots` the only legal ellipsis).
- **One engine end-to-end**: xelatex for print/gallery, xelatex→xdv→dvisvgm for web; plasTeX
  renders the four environments generically with per-body content-hash SVG caching (one edited
  figure invalidates one SVG, not 114).
- **Audit v2**: identity from `file:line`, not a registry; type-safety by construction in the
  grids; hard error on *empty pictures* (would have caught all 34 fake diagrams); advisories for
  repeated topology (suggests `\tndefine`), region-role stability, transfer-map canonicality;
  cross-engine drift checked by comparing canonical graph-hash multisets.
- **Migration in 4 phases, every call site compiling at every commit**: land beside old library →
  compat shim in 3 scripted PRs (34 empty entries become plain math; ~68 single-use entries get
  mechanical tenkz bodies; ~12 genuinely-reused entries become parameterized `\tndefine`s) →
  35 chapter-by-chapter inlining PRs → demolition of all of `tex/tn/` (~5,920 lines) plus the
  registry Python. Gates: pixel diff (with whitelisted intentional fixes) + event-graph
  isomorphism (waivable with one-line justification).
- **Manual as the citable artifact**, quantikz-structured: tutorial = benchmarks B1–B8, reference
  with per-command "why this is a command and not a key", the house-style chapter (glyph
  dictionary, canonical-spelling table, genre-ownership table), gallery = regression suite.

## 6. Five open questions for you (from the spec §8)

1. **Hull tracer**: if the expl3 notched-outline tracer stalls, accept a Python pre-computation
   helper in the TeX path, or restrict `outline` to simply-connected sets permanently?
2. **The named dozen**: do the ~12 multi-use `\tndefine` spellings stay permanently as house
   vocabulary in the blueprint preamble, or is full inlining the end state?
3. **Slides**: migrate decks to the `dark` theme within this project, or defer past Phase 3?
4. **Web accessibility**: whole-equation SVG reroute for inline atoms loses MathJax
   copyability — acceptable, or restrict inline atoms until an alt-text pipeline exists?
5. **Publication**: ship tenkz to CTAN/arXiv as a citable package at Phase-3 completion, or
   soak repo-internal for one release cycle first?
