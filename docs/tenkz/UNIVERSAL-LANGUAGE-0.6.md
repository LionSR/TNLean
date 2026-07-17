# tenkz 0.6 — THE UNIVERSAL LANGUAGE PROPOSAL

Chief-architect synthesis of the three principled reviews of the 0.5 surface
(torvalds: interface forks; tufte: ink economy and honesty; knuth: grammar and
naming), reconciled with the maintainer's abstraction-ladder brief (a
session working note, not in the repository) and the ranked 0.6 worklist
(`WORKLIST-0.6.md`, this directory).
Corpus counts below are measured over the 230 `.tex` files in
`scratchpad/tenkz_test/` (grep, sources only, logs excluded).

This document is the 0.6 interface contract as PROPOSED. Most of section
2 landed inside the unmerged-stack window; the rows the window did not
reach are marked in the status block after the table and move to 0.7.
`CHANGES-0.6.md` is the accurate record of the grammar as implemented.
Everything in section 5 phase B lands on top of the unified grammar,
never beside it.

The reviews agree on the diagnosis: the drawing engine has one language, the
key surface has three dialects. The brief's three unifications (frame, side
policy, contraction policy) exist in zero tiers today. The window is the one
chance to fix spellings by sed instead of by deprecation cycle. We take it.

---

## 1. THE GRAMMAR

### The sentence

> **A tenkz figure is a FRAME — one linear map from logical coordinates to
> paper — holding a stack of typed LAYERS (rows of a grid, sheets of a
> lattice) of CELLS at integer coordinates. Adjacent cells in a layer bond
> implicitly. Every index the picture creates is closed by a word from one
> POLICY ALPHABET — `pair | open | none | trace | cup | consumed` — applied at
> one of three scopes: interface segment, picture side, or row-at-side.
> Decorations (band-placed labels, braces, cuts, regions-as-cell-sets, roles
> and species) annotate ink and never own topology. The picture emits its
> boundary signature in the logical frame.**

489 of 556 corpus picture instances (~88%) are exactly this sentence already.
The grid is its 1D+physical instance; the lattice its 2D+sheets instance. The
0.6 work makes the key surface say the sentence in one vocabulary.

### The three policy families

**FRAME** (brief item 1). One key, `frame=flat|oblique|slab|vertical`, in both
grid and lattice. Presets are the interface; the mechanism is a 2x2 matrix
plus offset (`col vector=`/`row vector=`/`sheet vector=` remain the expert
override). The tracer is proven sound under any linear map. In the window the
grid implements `frame=flat|vertical` over today's involution and the lattice
renames `plane=` to `frame=`; routing the grid's remaining passes (spans,
cuts, bond labels, cups, traces) through the one map is phase-B work that
retires the vertical prune list. `orientation=` is deleted; `chain axis=`
survives as the chain-flavored alias.

**SIDE POLICY** (brief item 2). A picture side has exactly one policy:
`west=open|none|trace|cup|cup={$m$}` and likewise `east=` (lattice windows:
all four sides, `north=`/`south=` included). `consumed` is set by glyphs
(fuse, source bead), never written by users. `boundary=` is the all-sides
shorthand; `periodic` is the alias for `west=trace, east=trace`. Ink shape is
a separate how-key with no policy side effect: `trace style=racetrack|hooks`
(renamed from `periodic style=`, which today also *selects* periodic — a
how-key must never set the whether). Row scope is the `rows=` suffix instance
of the same enum: `rows={op:west none}` (worklist item 8 falls out of the
grammar), with `:open`/`:none` as both-sides row shorthands. The lattice
gains the identical keys, so worklist item 5 (inter-sheet east closure)
becomes `east=cup` pairing facing sheets exactly as grid cups pair facing
rows — a preset instance, not a planes-only invention.

**CONTRACTION POLICY** (brief item 3). Between facing layers, each interface
segment (interface, column) carries one state: `pair` (default, from typing) |
`open` | `trace`. One addressing algebra — the lattice's cell-set grammar
(terms, ranges, named regions, `+`/`-`) — serves every tier: `open={<cellset>}`
and `trace={<cellset>}` become picture keys of the grid too, resolved by the
same resolver. Grid interfaces are numbered top-down per adjacent facing pair;
the op row's self-trace interface is addressed by the word `physical`, so
`trace={(physical, 4-5)}` replaces `trace={physical at={4,5}}`. The cell key
`pair=trace` and the `at=` micro-sugar die; `nopair` survives as the row-scope
alias for "open on every segment of this interface".

One alphabet, three scopes, one addressing algebra. `trace` means the same
mathematics at a side (row closed onto itself) and at an interface segment
(site traced out); `open` means the same dangling index everywhere. That is
the whole language.

### The decoration algebra

- **Addressing**: the cell-set grammar is the single addressing algebra —
  regions, `open=`, `trace=`, per-bond and per-site records all consume it,
  in every tier. The third tuple slot means *sheet* in geometric records and
  *interface* in contraction keys; the manual states this distinction at the
  `open=`/`trace=` entries themselves (data model is correct; no second
  bracket syntax this close to the window).
- **Labels**: one placement vocabulary owned by the label doctrine. Every
  label — cell, `\tnput`, region, bond, span, cut, cup, boundary, join,
  tree — accepts `label pos=<eight winds + center>` and `label shift=`,
  placed in reserved bands, with the auto-quadrant chooser lifted into core
  as the every-tier default. An unknown compass word is an error, never a
  silent no-op. `label at=` demotes to an alias.
- **Hue**: roles and species (section 4). Semantic, themed, evented; no raw
  color at any call site, ever.
- **Skins**: one shared `/tenkz/skin` table consumed by every glyph parser:
  `dot|box|pill|mpo|tri=l|r|ring`, extended in 0.6 by the skin pack (blob,
  parallelogram, capsule, reroute). `\tnX` is the documented alias for the
  ring-skinned cell; the style's public name is `ring tensor`.
- **Events**: one format-version event at `\AtBeginDocument`; one coordinate
  field name (`cell=`) across emitters; signatures emitted in the LOGICAL
  frame (frame-invariant, so a vertical chain and its horizontal statement
  carry equal signatures); signatures count every open index, including
  `\tnskip` holes.

### Who stands outside the sentence, and why

- **tenkzcd** stands outside ON PRINCIPLE. Its cells are whole figures and its
  arrows are morphisms between figures — coherence-diagram mathematics, not
  contraction. It is the only family with an unknown-key passthrough, and that
  is now a documented property of being a tikz-cd wrapper, not an accident.
  It shares the metric doctrine and nothing else.
- **tenkzfree** stands outside ON PRINCIPLE as the escape hatch for genuinely
  non-grid geometry (MERA, braids, lassos). But the language's INVARIANTS
  cross the border: bare coordinates are pitch multiples (profiles rescale
  free figures like every tier), labels ride the band system, roles and
  species apply, and the tier emits a boundary signature (declared-but-
  unjoined ports are its open indices). What does not cross is the coordinate
  model — and pressure on the hatch (operator-hued wires, crossings) is
  relieved by growing the core grammar, never the hatch.
- **\tntree** is reclassified: it IS a contraction picture in word-syntax
  clothing. The parenthesization word stays as input syntax; the sentence's
  obligations (boundary signature: leaves up, root down; label doctrine)
  arrive in 0.6.

---

## 2. THE BREAKING CLEANUP LIST (unmerged-stack window)

Each entry: old spelling -> new, measured corpus cost, sed class. All seds run
once against the 230-file corpus before the stack merges; after merge every
one of these becomes permanent userspace.

| # | Old | New | Corpus cost | Migration |
|---|-----|-----|-------------|-----------|
| B1 | `close west[={m}]` / `close east[={m}]` | `west=cup` / `west={cup=$m$}` (likewise east) | 66+75 occ, 25+26 files | mechanical regex |
| B2 | `periodic style=X` selecting periodic as side effect | `periodic, trace style=X` | 12 occ, 4 files | mechanical; add `periodic` where the side effect was load-bearing |
| B3 | `orientation=horizontal\|vertical` | `frame=flat\|vertical`; key DELETED | 9 occ, 4 files | mechanical |
| B4 | `plane=flat\|oblique\|slab` (lattice) | `frame=` | 64 occ, 31 files | pure rename |
| B5 | `pair=trace` (cell key) | `trace={(i,c)}` cell set | 3 occ, 2 files | by hand, trivial |
| B6 | `trace={physical at={c,...}}` | `trace={(physical, c...)}` | 2 occ, 2 files | by hand, trivial |
| B7 | tenkzplanes fork (`/tenkz/planes/` family, own defaults, sheets= literal stub, missing header event) | true 5-line preset over tenkzlattice: `sheets={ket,bra}` + named frame preset (0.40/0.45 ratios) + `outer legs=none`; every accepted key is a `/tenkz/lattice` key; header event restored via `tenkzl_render:nn` | 90 occ, 11 files keep compiling | none at source; one render-diff review pass (defaults now flow from the preset, pending Q2) |
| B8 | `\tnsite` truthy option slot (any non-blank token removes the site) | real `/tenkz/site` family: `removed` as an actual key, room for `label=`, `role=`, `skin=`; unknown keys error | 46 occ `\tnsite[removed]`, 10 files, keep compiling | none for the corpus; junk options now diagnose |
| B9 | `\tnedge` dead option slot (parsed, discarded) | real `/tenkz/edge` family: `none` (bond suppression, worklist 7), `role=`, `label=`, `mark=squiggle`, `distinguished`; unknown keys error | 9 occ, 5 files re-examined by hand | small |
| B10 | `bond label={$D$ at 1-2}` micro-DSL (runaway on `at`-free values, probe-confirmed) | `bond label={label=$D$, at=1-2}` keyval; old form survives only under the strict padded-pattern rule, else errors helpfully | 21 occ, 15 files | mechanical |
| B11 | `rows=` modifiers matched by substring; row types unvalidated | token-parsed clist membership; unknown modifier or row type is an error naming the vocabulary | 0 (clean corpus unchanged) | none; typos stop being silent wrong ink |
| B12 | grid compass table missing east/west rows; unknown compass words draw nothing (probes 1-2); region `label at` unknown values draw nothing | 8-wind + center table in core, F-branch errors | 0 | none; adds a vertical-chain dot-label acceptance file |
| B13 | lattice `boundary legs` boolean | `boundary=open\|none` + four-side `west=/east=/north=/south=`; `boundary legs` aliased | 88 occ, 34 files unchanged | default flip pending Q1 |
| B14 | free-tier bare coordinates = raw tikz units, outside the metric doctrine | bare numeric pairs = pitch multiples; explicit dimensions remain the escape | 35 files | sed appends explicit units to every existing bare pair, preserving today's ink exactly; new figures speak pitch |
| B15 | `\tnghost{m}` mandatory dead argument (label recorded, never rendered) | `\tnghost`, argument-free | 190 occ; 178 are `\tnghost{}` whose leftover `{}` is a harmless empty group — zero forced cost; 12 non-empty arguments reviewed by hand (their labels never rendered) | optional hygiene sed |
| B16 | unknown-key policy varies (three families error, cd passes through) | error in every family; cd's passthrough documented as the deliberate tikz-cd wrapper property | 0 | none |
| B17 | `\tnfuse[rows=k]` (third meaning of `rows=`) | `span=k`; old spelling aliased | 0 forced | alias row |
| B18 | lattice `physical=` stops at `up\|none`; silent per-sheet legs in role-list stacks | choice set aligned with the grid (`up\|down\|updown\|none`, worklist item 2); in a role-list stack `physical=` errors pointing at `outer legs=` | acceptance test already written | small |
| B19 | event stream: no format version, `cell=`/`name=`/`site=` inconsistency, signatures skew under frames, skip holes uncounted, planes pictures headerless | format-version event; unified `cell=`; logical-frame signatures; hole accounting; header restored by B7 | audit layer only | none at figure source |
| B20 | silently dropped ink (vertical prune list, planes sheet substitution) warned only in the log | any pruned record stamps a passive-hue defect badge at the picture corner and emits a warning event; `\tnset{strict}` turns drops into errors; substitution (planes redrawing sheets=) is abolished — error with migration hint | 0 | none; honesty becomes visible |

Also in the window: `conjugate tensor` style wired to `\tn*` nodes (or the
dead slot deleted); `tenkz.sty` version string updated from "v0.1 Phase 0";
WHATS-NEW gap table refreshed (per-side control landed).

### Status of the section-2 rows (0.6 as shipped)

Landed in the window: B1–B9, B11, B13, B16, B17 (verified against the
shipped tiers; CHANGES-0.6.md records each surviving spelling and
alias). B12 landed in substance — the grid dot-label table now carries
the east/west rows and warns instead of dropping unknown words — though
the table lives in the grid tier, not yet lifted to core.

Deferred to 0.7, not shipped in the window:

- **B10** — `bond label=` keeps the `at` micro-DSL; no keyval form.
- **B14** — free-tier bare coordinates remain raw tikz units.
- **B15** — `\tnghost` still takes its mandatory dead argument.
- **B18** — lattice `physical=` still stops at `up|none`
  (worklist item 2 stays open).
- **B19** — no format-version event; the rest of the event unification
  shipped.
- **B20** — no defect badge, no `\tnset{strict}`; pruned records warn in
  the log only.

---

## 3. THE ALIAS TABLE (survives as documented sugar — one manual row each)

| Alias | Expands to |
|-------|-----------|
| `boundary=open\|none` | same word on every side (`west=`+`east=`; lattice: all four) |
| `periodic` / `boundary=periodic` | `west=trace, east=trace` |
| `chain axis=east\|south` | `frame=flat\|vertical` |
| `nopair` (row suffix) | `open` on every segment of that interface |
| `trace=physical` | trace every column of the op row's self-interface; topology (self-loop vs wrap) resolved from row-type data, not spelling |
| `physical=up\|down\|updown\|none` (grid) | `rows=` sugar |
| `sandwich` | `rows={ket,op,bra}` sugar |
| `:open` / `:none` (row suffixes) | `west <p>` + `east <p>` at row scope |
| `\tnX{m}` | `\tn[ring]{m}` |
| `boundary legs` (lattice) | `boundary=open` |
| `label at=` (region) | `label pos=` |
| `bond label={$D$ at 1-2}` | `bond label={label=$D$, at=1-2}` (strict pattern only) |
| `\tnfuse[rows=k]` | `\tnfuse[span=k]` |
| `tenkzplanes` | `tenkzlattice` preset: `sheets={ket,bra}`, planes frame preset, `outer legs=none` |
| `on-wire matrix` (style) | `ring tensor` |

Deleted outright, no alias: `orientation=` (a second first-class spelling is
the disease, not sugar), `close west/east`, `pair=trace`,
`trace={physical at=...}`, the `/tenkz/planes/` key family, `periodic style=`'s
policy side effect.

---

## 4. THE SEMANTIC HUE INTERFACE (decided)

Hue is semantic content and gets a semantic interface. Contract, five clauses:

1. **One role key, everywhere.** `role=operator|marked|extra|passive` is
   accepted by every glyph and wire command in every tier: `\tn[role=marked]`,
   `\tnput[role=operator]`, `\tnjoin[role=operator]`, `\tnsite[role=marked]`,
   `\tnedge[role=operator]`. The existing `rows={op:operator}` suffix becomes
   the row-scope spelling of the same key; `wires=k` glyphs take
   `wire roles={1:...,2:...}`. This clears worklist items 1 and 4 as instances
   of one key, not as per-tier patches.
2. **Species declare names, never colors.** `species={right,left}` declares
   names once (document preamble via `\tnset` or picture scope); the theme
   assigns hues from its semantic cycle. `rows={wire:species=right,
   wire:species=left}` is the whole of t2_twoshift's color content. Document-
   global declaration is recommended so a species keeps its hue across every
   figure of a paper.
3. **Resolution is pure style indirection.** Role and species map to derived
   styles in tenkz-core (one per role x glyph family, e.g. bond -> operator
   bond, tensor -> marked tensor). Themes rebind at one point. No `draw=`,
   no `color=`, no raw color word is ever exposed at a call site — in the
   free tier included.
4. **Closures inherit.** A closure (racetrack, hooks, cup, wrap loop) inherits
   the resolved style of the wire it closes. An operator-hued traced row draws
   an operator-hued ring (fixes t2_ared_loop).
5. **Hue is checkable data.** Every atom/join/bond event carries `role=` /
   `species=` fields; the audit checks that the two sides of an equation use
   identical species multisets. Color stops being decoration and becomes part
   of the boundary-signature discipline.

---

## 5. ORDERED 0.6 IMPLEMENTATION PLAN

Phase A is the window: breaking spellings, guardrails, and the corpus sed.
Phase B builds on the unified grammar; each item names the worklist entries it
absorbs. Nothing in phase B adds a key that phase A's grammar does not
predict.

### Phase A — inside the window (ordered; A1-A5 are merge-blocking)

- **A1. Side-policy alphabet.** `west=`/`east=` full enum in grid AND lattice
  (four-sided there); kill `close west/east` (B1); `trace style=` rename and
  side-effect removal (B2); row-at-side suffixes (worklist 8 lands here);
  `boundary legs` alias (B13). Corpus sed for B1/B2.
- **A2. Contraction cell-set unification.** Grid `open=`/`trace=` via the
  shared resolver; kill `pair=trace` and the `at=` sugar (B5, B6); `nopair`
  documented as alias.
- **A3. `frame=` spelling.** Grid `frame=flat|vertical` over the involution;
  lattice `plane=`->`frame=` rename (B3, B4); `chain axis=` alias; delete
  `orientation=`.
- **A4. Planes preset-ification.** Kill the `/tenkz/planes/` family (B7);
  role-list `sheets=` everywhere (B18's lattice `physical=` alignment was
  planned to ride along but did NOT ship — worklist item 2 remains open,
  the shipped choice set stops at `up|none`); default-sheet convention
  per Q2; header event restored.
- **A5. Strictness everywhere.** `/tenkz/site` and `/tenkz/edge` families
  (B8, B9 — prerequisite for worklist 6 and 7); token-parsed `rows=` mods and
  validated row types (B11); compass validation + east/west fix (B12);
  unknown-key policy (B16); `\tnghost` (B15); `span=` (B17); shared
  forward-to-core plumbing so pitch/compact/inline/tensor style work
  identically in every family.
- **A6. Label doctrine v1.** Core 8-wind + center placement table + reserved
  bands for ALL label kinds; auto-quadrant chooser lifted to core; `label at`
  alias; keyval `bond label` (B10).
- **A7. Free-tier metric.** Bare pairs = pitch (B14) + unit-preserving corpus
  sed.
- **A8. Honesty and events.** Defect badge + `\tnset{strict}` (B20);
  logical-frame signatures, hole accounting, format-version event, `cell=`
  unification (B19); free-tier and `\tntree` boundary signatures.
- **A9. Gate.** Full corpus sed applied; render-diff over all 230 files
  eyeballed once; WHATS-NEW-0.6 + USAGE updated; manual v2 ch6 key tables
  generated from the pgfkeys blocks (scope per Q3); `tenkz.sty` version
  string.

### Phase B — on the unified grammar (dependency-ordered)

- **B-1. Role/species hue system** (worklist 1 + 4; needs A8's event fields).
  Largest unblock: clears t2_eq50_pull, t2_eq54_ginj, t2_sptmpo_cross,
  t2_twoshift, t2_braidpat1 co-blocks; upgrades five more.
- **B-2. Multi-wire glyph leg completeness** (worklist 3).
- **B-3. Inter-sheet closures**: `east=cup` engine at the lattice tier
  (worklist 5; grammar landed in A1, ink lands here; with A4 clears
  t2_wrap9a).
- **B-4. Annotation content** on the A5 families (worklist 6): `\tnsite`
  labels, edge labels, squiggle marks, boundary-leg length override; and
  `\tnedge[none]` per-bond suppression (worklist 7).
- **B-5. Grid economy** (tufte): `sites=n` field-fill with typed default
  atoms, per-row labels in the suffix grammar, run-length cells; explicit
  cells override the field exactly as `\tnsite` overrides the lattice.
- **B-6. Composition** (worklist 10-13): `combined=` on `wires=k`, bare
  identity-wire atom, `\tnskip` robustness, routing gaps (cup-apex stub,
  hole turn-up, removed-site leg).
- **B-7. Equations and multiples** (tufte): `tenkzeq` container with shared
  baseline and relation event; `\tndef`/`\tnuse` named bodies; `tenkzrow`
  small-multiples container with sibling-diff audit.
- **B-8. Frame engine unification** (brief 1 completed): grid passes routed
  through the 2x2 map; vertical prune list and its defect badges retired;
  oblique grids for free.
- **B-9. Skin pack** (worklist 9, 14, 15): blob site + `physical=arrow`;
  off-lattice string primitive with over/under crossing gaps (free tier);
  region shapes (ellipse, circular blob); parallelogram, capsule, reroute,
  tree barbs, `\tnstub` port sugar.
- **Tail** (unchanged): directed signatures, mirrored `tri=` closures.

<!-- Hedge: B-5 and B-7 are the two items most likely to slip to 0.7 under
     schedule pressure; nothing downstream depends on them. B-1 through B-4
     are the tranche-2 unblockers and should not slip. -->

---

## 6. QUESTIONS FOR THE MAINTAINER (exactly three)

1. **Window boundary default.** The lattice draws clipped windows whose cut
   virtual bonds are, by the grid's own doctrine, open indices — yet
   `boundary legs` defaults off, rendering windows as sealed finite objects.
   Flip the default to `boundary=open` in the window (doctrine-honest;
   re-inks every existing window figure, one corpus re-render + eyeball), or
   keep sealed and correct the manual? **Recommendation: flip; the window
   exists for exactly this.**
2. **Default sheet for unaddressed cells in role-list stacks.** tenkzlattice
   puts a bare `(r,c)` record on sheet 0 (bottom); tenkzplanes puts it on the
   ket sheet (top state sheet — the school convention). One convention must
   win for all stacks and becomes permanent userspace. **Recommendation: top
   state sheet.**
3. **Merge gate.** Does the window close only after manual v2 ch6's key-table
   reference is generated from the pgfkeys blocks (drift-proof, delays merge),
   or may the stack merge on WHATS-NEW-0.6 + USAGE with ch6 generation as the
   first post-merge task? **Recommendation: gate on generation — it is
   mechanical, and the post-0.5 surface currently has no reference document
   at all.**
