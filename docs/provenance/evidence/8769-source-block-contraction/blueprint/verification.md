# Blueprint verification: joint source-input contractions

Source revision: `c80913b10d9926f31004705c78f136ade6b8b466`.
Pinned QICLean source: `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.
Chapter SHA256: `c5ff1f5bd492f4fd7fd771ae8720e27ea7fee46e3744f22d8acd8274c0f0b1fd`.

The five new Lean modules and the chapter were reviewed against their exact
mathematical statements. The joint contraction is obtained from an actual
allowed composition in a complete orthonormal basis, rather than inferred from
individual prepared-column bounds. The rectangular overlap has bra coordinates
as rows and ket coordinates as columns, and the trace pairing allows arbitrary
rectangular input matrices. Source-slot maps are independent of the prepared
vectors; their recovery identity has no normalization or contraction premise.
The separate contraction theorem permits proper frame images and needs no basis
of the target halfspaces. The pair count uses distinct complete unordered pair
coverage and assumes finite parties only for the cardinality conclusions.
These statements do not claim the subsequent chronological affected/exterior
circuit decomposition or the corrected-subset error bound.

## Exact source and declaration checks

- All 21 declarations in the final manifest occur exactly once in the chapter;
  all corresponding statement and proof completion tags are present.
- Canonical formatting, chktex, and reader-facing prose checks pass.
- Full mathematical source synchronization passes: 20,147 blueprint tag entries,
  20,153 distinct exported names, and 40,046 Lean declarations. The distinction
  between tag entries and names accounts for tags containing multiple names.
- The full dependency graph has 7,381 entries and 18,382 edges, with no duplicate
  entry labels or directed cycles.
- `snapshot-commit-check.json` records byte equality of 3,508 committed Lean,
  TeX, and bibliography sources and dependency-pin files against the revision
  above. The focused web entry point is deliberately replaced; the additional
  focused router and PDF entry point are disposable files. No other mathematical
  source was substituted. The source tree includes only the exact worktree
  sources and the pinned QICLean source copied from its earlier verified snapshot.

## Render checks

The focused document contains the pair-effects chapter and all six subsequent
source-preparation chapters through the present contribution. PDF and web
commands pass. The 20-page PDF's new chapter lies on physical pages 17–19;
all three were rendered to PNG and visually inspected. Formulas, indices,
headings and margins are legible and unclipped. Web generation reports no
warnings or errors. Browser checks pass on four generated HTML pages, covering
1,140 typeset expressions at the tested desktop and mobile widths.

The first render exposed a 12.8 pt overlong theorem-heading line. Replacing its
inline pair of norm hypotheses by the equivalent statement that both maps are
contractions removed this defect. Initial render records are retained under
`initial-render/`. The final PDF log retains only an inherited 0.99 pt overfull
line in the previously published common-source chapter (lines 221–230), outside
this change. There are no unresolved final PDF references or new overfull lines.

## Commands and scope

`commands.json` records exact commands, working directories, exit codes and
elapsed times for formatting, prose-related checks, complete source
synchronization, PDF generation, bibliography generation, and focused web
generation. `browser-command.json` records the browser test invocation.
`source-revision.json`, `source-sha256.json`, and
`snapshot-commit-check.json` identify the source bytes; `artifact-sha256.json`
identifies the resulting records and outputs.

This verification used a disposable source copy and changed no Lake build or
package cache. It did not perform a local Lake build or full-root
`leanblueprint checkdecls`. The exact imported-module Lean declaration and axiom
audit is recorded separately with the five-module proof verification.
