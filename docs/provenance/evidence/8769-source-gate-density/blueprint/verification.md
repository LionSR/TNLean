# Source-gate density: blueprint verification

The final chapter, all four production modules, the chapter router, and the
approximation import module were compared byte-for-byte with source revision
`86ed134591132d21ab3046d504e84196e2ee5ec6`. Exact hashes are in
`source-sha256.json`. Verification used a disposable copy of the density worktree
and the manifest-pinned QIC sources at
`8d5389d23c8e675a0117442e1a0d2c683a4bad41`, copied from the immutable source
snapshot used by the preceding common-space verification. No other live branch
supplied the declaration input. No Lake command or build-cache mutation was used.

## Results

- All 16 public declarations occur exactly once in the new fragment. The separate
  exact-source imported audit verifies these declarations in the four compiled
  modules; its reports contain only the three standard axioms.
- Canonical latexindent, chktex, and reader-facing prose checks pass on the exact
  final chapter. Full declaration synchronization passes for all 20,126 reference
  entries against 40,016 parsed Lean declarations. The generated reference list
  has 20,132 distinct names; individual names and reference entries are different
  counts.
- The full dependency graph has 7,370 nodes and 18,356 edges,
  with no duplicate labels or cycles. The new chapter's dependency edges are
  recorded in `dependency-graph.json`.
- The focused PDF renders all six consecutive source-preparation chapters in
  18 pages. Pages 14–17, containing the new chapter, were inspected visually.
  A long product identity was moved to a displayed formula to remove its
  33.59pt overflow; the corrected final render has no new overflow, clipping,
  missing symbols, or unresolved references. The unchanged preceding common
  chapter retains one harmless 0.99pt overfull line.
- The web render completes without warnings or errors. The repository's browser
  checks pass at the prescribed desktop and mobile widths on all four generated
  pages, typesetting 1,009 expressions.

## Mathematical review

The preparation sum is derived from the actual source vector's multilinearity.
Its finite component families may span proper subspaces. Ket and bra endpoint
indices are independent; each bra coefficient is conjugated exactly once. The
weighted formula retains the original coefficients and their bra conjugates.
No density identity assumes positivity or normalization of the input matrix.

The final theorem starts with the original allowed branch words. It constructs
common finite source coordinates and allowed remaining words containing no
sources, proves their exact recovery of the original operators, and derives
contraction bounds for the elementary prepared matrices. Every witness is
chosen before the universal quantifier over the input matrix. The matrices on
the left side are the matrices of the original words, not independent supplied
coefficients. The theorem does not claim the Gaussian replacement, the joint
free-source block contraction, or the circuit error estimate.

Exact commands, durations, source hashes and graph data are retained beside this
report. This is full source-reference synchronization and focused rendering,
together with the separately recorded imported 16-declaration audit. It is not
an execution of full-root `leanblueprint checkdecls` or a local Lake build.
