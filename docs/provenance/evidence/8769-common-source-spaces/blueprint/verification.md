# Common private source spaces: blueprint verification

The final chapter and its predecessor fragments were checked in a disposable copy of
`worktrees/peps-common-source-spaces`. The nine Lean modules were verified separately at
`b8864ae6ca2a3fbd5ecf0989e682a38d33ee02a6`; the final chapter correction and propagated
predecessor prose fixes are identified by exact SHA256 values in `source-sha256.json`.
The enclosing predecessor merge is `53630b1f37940bc5c8f3eadd3aa527d5ea99b3e8`.
The QIC source used in synchronization was extracted from the manifest-pinned revision
`8d5389d23c8e675a0117442e1a0d2c683a4bad41` into the disposable directory. It was not read
from another moving branch. No Lake command or build-cache mutation was performed.

## Results

- All 34 declared exports occur exactly once in the new fragment; `tag-coverage.json`
  records the correspondence. Their compiled existence and standard-axiom audit are
  supplied by the separate 34-declaration imported audit of the nine source modules.
- Canonical latexindent, chktex, and reader-facing prose checks passed on the exact
  final new chapter. The full source synchronization passed for all 20,110 blueprint
  reference entries against 39,985 parsed declarations. There are 20,116 distinct
  names in the generated full declaration-reference list; these counts differ because
  entries and individual names are distinct quantities.
- The full dependency graph has 7,361 nodes and 18,336 edges, no duplicate labels,
  and no cycles. The new chapter's dependency edges are recorded explicitly.
- The focused PDF includes all five source-preparation chapters and has 15 pages.
  Pages 11–14, containing the new mathematics, were inspected visually: equations,
  references, symbols, and paragraph breaks are legible without clipping. TeX reports
  one 0.99pt overfull line; its rendering has no visible collision or clipping.
- The web render completed without warnings or errors. The repository's browser
  checks passed at the prescribed desktop and mobile widths on all four generated
  pages, typesetting 826 expressions (`browser.log`).

The statements agree with the Lean signatures: recovery is uniform over the spectator
memory, while its actual recovery word may depend on that memory; the branch index
may be empty; source ordering and endpoint orientation are derived; finite coordinates
are obtained from the finite family of algebraic tensor vectors without an ambient
finite-dimensionality assumption. Zero coordinate dimensions are allowed. The final
input identification includes fresh source registers, whereas the output identification
groups only the original output registers. No bound on private dimensions or completed
sampling argument is claimed.

This is source synchronization, focused rendering, and a reference to the imported
34-declaration audit. It is not a full-root `leanblueprint checkdecls` run or a local
Lake build. Exact rendering commands and durations are in `commands.json`; the browser
retry adds the required Playwright dependency without changing the Lean environment.
