# Blueprint verification: free source inputs and untouched exterior gates

Source revision: `8689eafdd341540d4dd7e6848707646d6e3a0970`.
Pinned QICLean source: `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.
Chapter SHA256: `96d9214dc23b09868a5bee58fa52dcc11e7e3f7262e4613cebb3bd7a128e86b6`.

The chapter was independently reviewed against all six source modules. Common
finite gate data are derived from the original allowed branch words and their
original aggregate contraction hypothesis. The scalar coefficients are fixed
before choosing the source representation. Completion of source positions is
only over each gate's participating party type. The exact owner identification
retains the aggregate operator and its norm bound, without estimating it by the
sum of absolute branch coefficients.

Every affected party remains a distinct owner, while exterior parties acquire
one common owner. Surviving source occurrences retain their original spaces,
vectors, order and multiplicity. The criterion for survival is that at least
one endpoint is affected. Selective preparation normalizes only fixed sources;
the two local factors are chosen before every possible family of free vectors.
Their first operator identity holds on the whole free-input memory. The same
factors then recover every completed preparation. Spectator extension is the
actual exchange–frame–exchange composition and has exactly the original source
inventory. The chapter leaves the chronological partial expansion and the
corrected-subset trace-norm estimate as separate obligations.

## Exact source and declaration checks

- All 37 explicit public declarations in the final manifest occur exactly once
  in the chapter. Statement and proof completion tags are present.
- Canonical formatting, chktex, and reader-facing prose checks pass.
- Full mathematical source synchronization passes: 20,212 blueprint tag entries,
  20,218 distinct reference names, and 40,152 Lean declarations. Tags containing
  multiple declarations account for the first two counts being different.
- The full dependency graph has 7,408 entries and 18,439 edges, with no duplicate
  entry labels or directed cycles.
- `snapshot-commit-check.json` records byte equality of 3,521 committed Lean,
  TeX, and bibliography sources and dependency-pin files against the revision
  above. The focused web entry point is deliberately replaced; the additional
  focused router and PDF entry point are disposable files. No other mathematical
  source was substituted. The snapshot contains exactly the six new source
  modules and the current generated import aggregators. No subsequent
  chronological-circuit prototype is included.

## Render checks

The focused document contains the pair-effects chapter and subsequent
source-preparation chapters through this contribution. PDF and web commands
pass. The new section occupies physical pages 21–24 of the 25-page PDF. All
four pages were rendered to PNG and visually inspected: formulas, indices,
headings, references and margins are legible and unclipped. Browser checks
pass on four generated HTML pages, covering 1,495 typeset expressions at the
tested desktop and mobile widths. Web generation reports no warnings or errors.

The final TeX pass has no unresolved references or new overfull lines. It
retains only the inherited 0.99 pt overfull line in the previously published
common-source chapter (lines 221–230), outside this change. `final-tex.log`
records that final pass. `pdf.log` records the entire multi-pass invocation,
including reference warnings which were resolved by the subsequent passes.

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
audit is recorded separately with the six-module proof verification.
