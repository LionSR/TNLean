# The goal

<!-- The standing prompt for any agent or contributor taking up the
     tensor-network diagram effort. Load this first; HACKING.md second.
     Everything here is doctrine the maintainer has stated and enforced. -->

You are working on **tenkz**, the tensor-network diagram language of the
TNLean blueprint. Hold three masters in mind at once: **Knuth** — the
source is literate, every constant is named and motivated, the manual is
the contract; **Tufte** — ink is data, one mark has one meaning, labels
never touch wires, families are enumerated small multiples, extend a good
element rather than invent a new genre; **Torvalds** — no special cases,
measure instead of predict, one data source per question, delete twins.

## What the library is for

TNLean formalizes the fundamental theorem of matrix product states,
quantum Wielandt theory, and quantum-channel theory in Lean 4. The
blueprint is the mathematical document reviewers read; its diagrams must
be publication-grade and paper-faithful. tenkz exists for that — it is
infrastructure in service of a formalization, and it is finished when the
blueprint is served (milestones 0.6–1.0; the backlog does not extend it).
The diagram is the primary carrier of a pictured identity; the formula
lives beside it and always in the `%` comments.

## The non-negotiables

1. **Mathematical correctness is paramount.** Every figure states its
   formula and ink-to-index correspondence in `%` comments. Both sides of
   a pictured equation carry one boundary signature. No open legs is a
   scalar; a map keeps its legs open. The applied channel is
   `[sandwich, east={cup=$X$}]` — a west cup feeds the adjoint. Never
   draw what the cited source does not assert; an honest **blocked**
   beats a faked figure.
2. **One universal language.** One frame key, one side-policy alphabet,
   one cell-set algebra, in every tier. A new capability extends the
   existing vocabulary (Tufte, *Beautiful Evidence* 76–77) or it waits.
3. **Measured, not budgeted.** Clearance questions go through the
   silhouette resolver plus the one daylight constant (historical rationale:
   `history/DESIGN.md` §18).
   Never add a constant that predicts what another pass draws.
4. **Verification is visual.** Exit codes do not review figures — render
   and look, against the cited paper's own figure when one exists.
5. **Periodic simplification is scheduled work.** The gate (issue #4158)
   runs before every milestone closes: what grew ad hoc, which two
   things are one thing, what would a redesign delete. Finding nothing
   fails the gate.
6. **No whole-figure motif macros in chapters.** Chapters write inline
   tenkz bodies; the grammar is the interface.
7. **Prose is confident** (Strunk & White). Hedges, caveats, and
   self-murmuring live in `%` comments, never in rendered text. Blueprint
   prose is pure mathematics — no Lean identifiers, no software jargon.

## Where everything lives

- `docs/tenkz/LANGUAGE.md` — the public mental model and semantic rules.
- `docs/tenkz/DESIGN.md` — compatibility, version, release-tag, and soak
  policy; `SOAK-1.0.md` is its append-only release ledger.
- `tex/tenkz/tenkz-language-registry.tex` — the executable vocabulary.
- `docs/tenkz/manual2.tex` + `chapters2/` — the compact citable manual and
  generated canonical reference.
- `docs/tenkz/ARCHITECTURE.md` — internal pipeline and ownership boundaries.
- `docs/tenkz/HACKING.md` — build and debugging procedure; read it before
  editing any `.code.tex`.
- `docs/tenkz/history/` — superseded design proposals, reviews, migration
  inventories, and 0.6 worklists; historical context, not current syntax.
- GitHub milestones 0.6–1.0 with their issues — the sequence. The spine
  is the stack landing (#4151); after it, only small PRs off `main`.
- `tex/tenkz/*.code.tex` — staged implementation from language and model
  through style, geometry, dialect layout, rendering, and events.

## How to decide

When a figure needs something the language lacks, first ask whether an
existing element extends (a key, a policy word, a cell-set); design the
general element or file the gap — never special-case one figure. When
two mechanisms answer one question, merge them or write down why not.
When infrastructure competes with the mathematics for attention, the
mathematics wins: close the loop you are in, land it, and return to the
formalization queue.
