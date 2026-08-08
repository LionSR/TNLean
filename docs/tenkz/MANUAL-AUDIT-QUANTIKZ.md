# Auditing the tenkz manual against quantikz

Issue #5356. quantikz is the reference point for what a mature TikZ-family
diagram package teaches its users; this register compares the current tenkz
manual against it finding by finding, and closes with the prioritized
worklist that the #4708 manual rewrite executes. It changes no manual text
itself.

Documents compared:

- **quantikz**: Alastair Kay, *Tutorial on the Quantikz Package*,
  arXiv:1809.03842, dated 24 May 2023 — the PDF documentation CTAN ships.
  27 pages, sections I–X. Section/page citations below refer to this build.
- **tenkz**: `docs/tenkz/manual2.tex` with `chapters2/`, built at commit
  `b2b13e60d` with the documented invocation
  (`TEXINPUTS="../../tex/tenkz//:" xelatex manual2.tex`, twice). 20 pages.
  Page citations below refer to that build.

## 1. Method

Four measurements, each reproducible from the tracked tree:

1. **Full read of both manuals** from the rendered pages, not the source
   alone: all 27 quantikz pages, all 20 tenkz pages, with page images
   inspected for the figure-density and first-picture findings.
2. **Registry cross-check.** Environments, commands, and keys were extracted
   from `tex/tenkz/tenkz-language-registry.tex` (4 environments, 22
   commands, 150 key rows: 144 canonical plus 6 sunset aliases) and each
   canonical name was searched for in the authored chapter sources
   (`chapters2/ch-*.tex` and `manual2.tex`, generated tables excluded).
3. **Example census.** Displayed example environments were counted per
   chapter: 5 `tnexample` blocks (rendered output plus source), 9 `Verbatim`
   blocks (source only), 0 `tnmultiples` blocks.
4. **Build check.** `manual2.pdf` compiles clean; every displayed block is
   compiled standalone by `scripts/tenkz_manual_doctest.py`.

Numbers used throughout: quantikz sets more than forty boxed examples in 27
pages, nearly all with the rendered output beside the source; tenkz sets 5
rendered examples and 9 source-only blocks in 20 pages.

## 2. Coverage — what quantikz teaches that the manual does not

**F1. The 1.0 kernel surface has zero rendered pictures.** Every one of the
five rendered examples (tutorial §3.1–§3.4, recipe §4.2) is written in the
0.7 grid dialect. All six kernel-surface examples — `ch-worked.tex` §4.5,
§4.6, §4.7, §4.8 and `ch-house.tex` §6.1 open with `\tenkzkernel` — are
`Verbatim` blocks whose output the reader never sees. quantikz pairs every
construct with its render from the first wire onward (§II, p. 2). The
surface the 1.0 release ships is the one surface the manual never pictures.

**F2. `tenkzeq` is undocumented.** The equation-composition environment with
the boundary-signature audit — a headline capability of the kernel contract
(`LANGUAGE-1.0.md`) and a registered environment — appears in no chapter, no
tutorial, no recipe, and no reference table. Its only trace in the built
manual is the phrase "the tenkzeq audit specification" in the meaning column
of the `check` key row. quantikz devotes §IV.C plus §IV.C.1 (pp. 15–17,
four worked examples) to exactly this task: typesetting circuit identities
with aligned equals signs. Our equation story (`ch-tutorial.tex` §3.3) still
composes pictures with bare TeX and mentions the audit in passing prose.

**F3. No spacing or metric chapter.** quantikz §IV (pp. 14–17) teaches
local column/row adjustment, global `row sep`/`column sep`, `between
origins`, and phantom-based sizing, each with a render. The tenkz metric
vocabulary — `pitch`, size classes (`size=`, `sizes=`), `layer sep`,
`align`, `nudge`, the `inline` profile — is documented only as reference
table rows; no chapter shows what any of them does to a picture, and
`kernel-setup pitch`, `sizes`, `layer sep`, and `align` never occur in an
authored chapter at all.

**F4. No styling catalogue.** quantikz §V.A (p. 18) prints the table every
styling question needs: style name against affected commands, then global
restyling via `tikzset` and per-gate overrides, each rendered. tenkz has the
better semantic model (themes, species, roles, slots) and no equivalent
catalogue: nothing states what ink `theme=house` binds, what the house hue
cycle is, which slots exist for regions and marks, or what a `species`
declaration changes, and `theme=` never occurs in an authored chapter.

**F5. No migration narrative.** quantikz §VII (pp. 24–25) gives a
conversion table (QCircuit spelling to quantikz spelling) plus a bulleted
breaking-change list for quantikz 0.x to 1.x. The tenkz compatibility
appendix quarantines the six alias spellings with their sunsets — the right
structure — but no worked example converts a 0.7 grid figure to its kernel
spelling, which is the conversion every blueprint figure and the corpus
rewrite will perform at the S4 swap.

**F6. No compile-error phrasebook.** The troubleshooting chapter's
symptom table (`ch-trouble.tex`) is well structured, but every entry is a
semantic symptom. quantikz §VIII (p. 25) also covers the compile-time
failure shapes ("cells not being found", the trailing `\\` trap, package
load order, the literal error text "Only one # is allowed per tab"). The
tenkz registry carries a representative failure per command and the test
suite pins 108 coded negative fixtures, yet the manual never quotes one
actual diagnostic message; a user who hits a hard error cannot find its
text in the manual.

**F7. No citation or version statement.** quantikz §X tells the reader what
to cite. The tenkz manual states no version, no release policy pointer, and
no citation form. One sentence each; the 1.0 announcement draft
(`ANNOUNCEMENT-1.0-draft.md`) already contains the material.

**F8. No index — in either manual.** quantikz offers only its contents
page. For a compact manual that parity is acceptable; for the full-length
1.0 manual the doctrine demands (the kernel shrinks, the manual deepens),
the pgf manual is the precedent, and an index or at least a key-name
finding aid belongs in the rewrite plan — decided explicitly, not by
omission.

**F9. Externalization and large-document workflow: defer with rationale.**
quantikz §VI.A (p. 21) covers `tikzexternalize` for slow documents. The
tenkz consumer is the blueprint build, which manages its own pipeline, and
the manual's audience is not typesetting hundred-figure articles by hand.
Defer, and record the deferral here as #5356 requires. The same disposition
covers quantikz §IX (web interface): the XDV-to-SVG route is stated in
§1 of the manual and the blueprint owns the rest.

**F10. Gallery: served elsewhere, deliberately.** quantikz has no gallery;
tenkz has a 130-target benchmark book with per-target source, render, and
verdict, kept out of the manual by design (`ch-rmp.tex`). No action; the
field-guide chapter already cross-references it.

## 3. Pedagogy — how each manual sequences learning

**F11. First picture: tenkz wins, then goes silent.** tenkz renders three
diagrams on the title page and holds a picture-per-page pace through page 6.
quantikz shows its first render on page 2 and then never stops: pictures
continue to its last content section. In tenkz the last rendered diagram
in the body is Example 4.1 on page 6 — pages 7 through 20, seventy percent
of a diagram language's manual, contain no rendered diagram.

**F12. The tutorial teaches the outgoing surface, and the reader meets the
kernel unintroduced.** The four tutorial examples are 0.7 grid spellings;
`\tenkzkernel` first appears mid-recipe (§4.1, p. 5) inside a discussion of
boundary defaults, with no statement of what the switch is, why two
surfaces exist, or which one a new figure should use. quantikz2 had the
same two-surface problem and answered it in its opening abstract and §VII.A
(p. 24). The two-surface story exists only as comments in the registry and
in `LANGUAGE-1.0.md`.

**F13. The tutorial announces five examples and delivers four.**
`ch-tutorial.tex` opens "The five examples use the same reading order" and
contains four subsections (§3.1–§3.4). Either the missing fifth — the
natural candidate is a `tenkzeq` equation with `check=` closing both F2 and
F12 — or the count is corrected.

**F14. Recipes narrate where quantikz demonstrates.** The recipe chapter's
prose-to-picture ratio inverts quantikz's. §4.1 (keep a map open) resolves
a genuinely subtle default divergence entirely in prose; §4.3 and §4.4 are
pictureless; §4.5–§4.8 show source only. Each of these is one rendered
example away from being self-checking: the reader should see the sealed
scalar next to the open map, the role next to the species, exactly as
quantikz renders both the ugly and the fixed spacing in §IV (p. 15).

**F15. The quick-reference card is a real advantage with one stale row.**
quantikz has no cheat-sheet; the tenkz back-page card is the better design.
It cites `tenkz_rmp.sh` under Verification; the script is
`scripts/tenkz_rmp.py` (the `.sh` frontend is deleted). This is the one
surviving instance of the stale-teaching class #5356 orders removed — the
`tenkzfree`/millimetre/`out=`-`in=` sweeps are already clean.

## 4. Reference completeness — registry against manual

**F16. The reference chapter has no environments table.** The registry
declares four environments (`tenkz`, `tenkzlattice`, `tenkzplanes`,
`tenkzeq`); the generated reference (`generated-language-reference.tex`)
contains a commands table, a keys table, and a prelude table — no
environments. quantikz §III opens with the environment entry, options
first (p. 7).

**F17. Command examples are pointers, not examples.** Each of the 22
command rows prints the path of its standalone example
(`tex/tenkz/examples/api/*.tex`) instead of the example. quantikz §III
(pp. 7–14) prints a source-plus-render box under nearly every command
entry. The generator (`scripts/tenkz_language.py`) already knows the file;
inputting and rendering it is the missing step.

**F18. Zero of 150 key rows carry an example.** The keys table gives scope,
type, default, and a one-clause meaning — useful as an inventory, unusable
as instruction. Cross-checking key names against the authored chapters: 83
of 144 canonical keys never occur anywhere in the manual outside their
generated table row — not in a tutorial, recipe, or even prose mention.
The worst-served scopes are precisely the kernel's: `kernel-wire` (11 of 14
keys unshown, including `kind`, `via`, `cross`, `crossing`, `dir`,
`stroke`, `closed`), `kernel-picture` (10 unshown, including `trace`,
`open`, `ring`, `surface`, `planes`, `lattice`, `check`), and
`kernel-atom` (7 unshown, including `wide`, `wires`, `void`, `cluster`).
By contrast quantikz documents each command's option list with at least
one rendered use of the command those options modify.

**F19. `tnmultiples` is defined and never used.** The manual style ships a
small-multiples environment (one source, several variant panels) that is
exactly the instrument for teaching enum-valued keys — `boundary=`,
`route=`, `stroke=`, `form=`, size classes — one family per figure, per the
Tufte doctrine in `GOAL.md`. Zero uses in the manual. quantikz teaches
enum keys by repeating whole boxes (§II.B controlled gates, p. 3); the
tenkz instrument is better and idle.

**F20. Copy-paste success: tenkz is ahead and should say so.** Every
displayed block is compiled standalone by `tenkz_manual_doctest.py`, so a
pasted example cannot silently rot; quantikz has no such guarantee (its
§VIII opens with the `{}` trap its own examples must avoid). The manual
never tells the reader that every printed example is build-verified — one
sentence in §1 would convert an internal gate into a user promise.

## 5. What tenkz does better — kept, on purpose

These are the deliberate #4104 design decisions the rewrite must preserve;
they are findings in quantikz's column.

- **Formula-first margin apparatus.** Every rendered example carries the
  formula, the ink-to-index legend, and the audited boundary signature in
  the margin (e.g. Example 3.1, p. 3). quantikz never states what a circuit
  means; no example in its 27 pages equates a picture with an expression.
- **Output-first example boxes** with pedagogic `%` comments that print in
  the manual and vanish in the render.
- **A decision procedure, not a feature tour.** The environment chooser
  (`ch-modes.tex`) chooses by topology with a recognition test per row;
  quantikz has no guidance for choosing among its environments or when not
  to use one.
- **An executable registry as the single source of the reference.**
  quantikz §III is hand-maintained prose that can drift from the code;
  the tenkz reference cannot drift, only under-render (F16–F18).
- **A principled extension story.** `\tndeclare` with typed ports and the
  three-consumer gate (`ch-house.tex`) against quantikz §VI.B's four pages
  of raw pgf anchor arithmetic that its own author calls fiddly (pp.
  21–24).
- **Alias quarantine with sunsets** as generated data (appendix), against
  prose-only conversion notes.
- **A tested negative-space.** Representative failures are registry data
  and 108 negative fixtures pin coded diagnostics; quantikz documents
  failure modes anecdotally.

## 6. Worklist for the #4708 rewrite

Ordered; each item names the findings it discharges and its quantikz model.

1. **Rewrite the tutorial and recipes on the kernel surface, and render
   everything.** Tutorial examples become kernel spellings with the margin
   apparatus kept; the six `Verbatim` recipes become `tnexample` blocks;
   the two-surface story (and the S4 swap's effect on spellings) is stated
   where the reader first needs it; the fifth tutorial example is the
   `tenkzeq` identity with `check=`. Model: quantikz §II + §IV.C.
   Discharges F1, F2 (tutorial half), F11–F14.
2. **Regenerate the reference to render what it inventories.** Add the
   environments table; input and render each command's standalone example
   in place of its file path; give every key family a rendered example,
   using `tnmultiples` for enum-valued keys. The backlog measure is the 83
   never-shown keys; the target is zero rows without a reachable rendered
   example. Model: quantikz §III. Discharges F16–F19.
3. **Write the composition-and-metric chapter.** `pitch`, size classes,
   `align`, `layer sep`, `nudge`, the `inline` profile, equation alignment
   through `tenkzeq`, small multiples as house method. Model: quantikz
   §IV. Discharges F2 (chapter half), F3.
4. **Write the styling catalogue.** Theme/species/role/slot against the ink
   each binds, the house hue cycle, one global-restyle and one per-object
   example. Model: quantikz §V.A table, p. 18. Discharges F4.
5. **Add the migration spread.** One 0.7-grid figure and its kernel
   spelling side by side, plus the alias appendix as is. Model: quantikz
   §VII. Discharges F5.
6. **Add the diagnostic phrasebook.** Quote the actual message text of the
   dozen most-hit coded diagnostics with their first corrections, sourced
   from the negative fixtures. Extends `ch-trouble.tex`. Discharges F6.
7. **Small honest fixes, one sitting.** `tenkz_rmp.sh` to
   `scripts/tenkz_rmp.py` in the quick-reference card; the doctest promise
   stated in §1; citation and version sentence. Discharges F7, F15, F20.
8. **Decide the index.** Yes/no with rationale recorded against F8; a
   key-name index generated from the registry is the cheap strong option.
9. **Record the deferrals.** Externalization, accessibility, and web-UI
   chapters are deferred per F9–F10; this register is the rationale #5356
   requires before #4163 closes.

Scale, for planning the rewrite: reaching quantikz's demonstration density
on our larger vocabulary (170 canonical constructs against quantikz's ~40)
means roughly 40–50 rendered examples against today's 5, and roughly
doubling to tripling the 20-page manual — consistent with the standing
directive that the 15-page compact form is too thin for 1.0 and the manual
is a full-length work.
