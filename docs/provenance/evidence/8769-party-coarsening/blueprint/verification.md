# Blueprint verification: grouping parties and internal preparations

Source revision: `2609edd456a91c7d5b34e23b0b8a7e3d8626f54f`.
Pinned QICLean source: `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.
Chapter SHA256: `9ed01faa8a6f3a0eb233001a90a88c661d1ec07eaf0feedd6712a7fa0f75dacc`.

The five new Lean modules and the chapter were reviewed against their exact
mathematical statements. Grouping arbitrary party labels preserves every
register and the operator of each actual composition, through canonical memory
isometries. A source whose endpoints acquire the same owner becomes a local
preparation of the same vector. Only its occurrence in the pair-source list is
removed. Surviving sources retain their spaces, vectors, order and multiplicity.
The exact operator identity needs no normalization, finiteness or injectivity
assumption. Normalization supplies the local contraction bound for an internal
preparation.

The two-side theorem explicitly assumes that both endpoints of every original
source lie on the same side. Its witnesses are the actual two restrictions of
the grouped composition, and their tensor product recovers the original
operator. Source absence and contraction bounds are proved, not hypothesized.
These results do not yet construct the chronological partially expanded circuit,
its selective source preparation, or the compression error estimate.

## Exact source and declaration checks

- All 28 declarations in the final manifest occur exactly once in the chapter;
  the corresponding statement and proof completion tags are present.
- Canonical formatting, chktex, and reader-facing prose checks pass.
- Full mathematical source synchronization passes: 20,175 blueprint tag entries,
  20,181 distinct reference names, and 40,085 Lean declarations. Tags containing
  multiple declarations account for the first two counts being different.
- The full dependency graph has 7,390 entries and 18,400 edges, with no duplicate
  entry labels or directed cycles.
- `snapshot-commit-check.json` records byte equality of 3,514 committed Lean,
  TeX, and bibliography sources and dependency-pin files against the revision
  above. The focused web entry point is deliberately replaced; the additional
  focused router and PDF entry point are disposable files. No other mathematical
  source was substituted. The snapshot includes exactly the five new coarsening
  modules. The subsequent uncommitted selective-preparation file is excluded.
  The generated import aggregators agree exactly with the source commit.

## Render checks

The focused document contains the pair-effects chapter and the subsequent
source-preparation chapters through the present contribution. PDF and web
commands pass. The 22-page PDF's new section occupies physical pages 19–21;
these pages and the following bibliography were rendered to PNG and visually
inspected. Formulas, indices, headings and margins are legible and unclipped.
The final displayed factorization has correct closing punctuation. Web
generation reports no warnings or errors. Browser checks pass on four generated
HTML pages, covering 1,272 typeset expressions at the tested desktop and mobile
widths.

The final PDF log retains only an inherited 0.99 pt overfull line in the
previously published common-source chapter (lines 221–230), outside this change.
There are no unresolved final PDF references or new overfull lines.

## Commands and scope

`commands.json` records exact commands, working directories, exit codes and
elapsed times for formatting, complete source synchronization, PDF generation,
bibliography generation, and focused web generation. `prose.json` records the
reader-facing prose check. `browser-command.json` records the browser test.
`source-revision.json`, `source-sha256.json`, and
`snapshot-commit-check.json` identify the source bytes; `artifact-sha256.json`
identifies the resulting records and outputs. The copied setup, verification
and source-comparison drivers record the isolated rendering procedure.

This verification used a disposable source copy and changed no Lake build or
package cache. It did not perform a local Lake build or full-root
`leanblueprint checkdecls`. The exact imported-module declaration and axiom
audit is recorded separately with the five-module proof verification.
