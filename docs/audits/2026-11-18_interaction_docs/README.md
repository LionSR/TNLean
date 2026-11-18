# Documentation lane: canonical Interaction migration

Base: `b2c72008326f3166d3bcdc9e79013443142b0aa8`.
QICLean pin: `729428582b78ab7529b3796099193649f947354a` (unchanged).
Branch: `codex/interaction-docs-b2c72008`.

This is a documentation-only intermediate contribution, not a merge-ready
integration. The shared contract and all production/fixture files are unchanged.
The exact base already includes main `7376dab08421ab99afcc5373be11104c76cc8a50`,
the #10816 merge. Neither existing PR nor an external author's branch is edited.

## Coverage

`coverage.tsv` accounts for all 34 assigned paths: 32 without textual conflicts
and the two conflicting Blueprint chapters. The 233-path allocation was checked
as a disjoint partition (34 documentation, 6 shared, 86 MPS, 107 PEPS). This does
not constitute semantic review of the other 199 paths.

Canonical names and sum declarations replace removed bundled-owner names. Dead
bundled zero/accessor tags are removed; there is no shim. Mathematical statements
retain their original hypotheses and conclusions, with these explicit corrections:

- PlaneInteraction/ChainInteraction/DomainInteraction carry supported terms;
  Hermiticity and norm bounds are hypotheses, not fields. The plane model's
  definition admits real J; actual positive-gap area-law hypotheses remain.
- Rectangular transport retains total Hermiticity, arbitrary J and Δ, and the
  norm/PSD/member statement. Its separate Hermiticity/norm-preservation results
  are linked. Main's `ManyBody.ChainSupport.edist_le` correction is retained.
- The IsSquareGroundState description now correctly records norm/PSD/member,
  with uniqueness derived only at positive Δ. The box note distinguishes a
  positive-size integer rectangle from an empty physical intersection and
  retains the conditional hbox and exponent assumption.
- The architecture document adds a dated update without rewriting its historical
  counts, old structure names or F12 account. These are explicitly historical.

`FIXTURE_ACCEPTANCE.md` provides the independently prepared five-family signature
and boundary checklist. It is separate from the shared API contract. No fixture
has been edited, deleted, compiled or claimed passing by this documentation lane.

## Checks actually performed

- `git diff --check`: passed.
- Pinned `scripts/latexindent` 3.24.7 on temporary copies of all 22 assigned
  Blueprint files: passed; no formatting changes were needed (`format.json`).
  The initial default cache location was read-only; the same wrapper then ran
  successfully with `XDG_CACHE_HOME=/tmp/interaction-docs-cache`.
- `python scripts/blueprint_roles.py --check`: passed.
- All 34 files preserve the sequence and payload of label/ref/eqref/uses/cite
  commands from the base (`reference-preservation.json`, before/after hashes).
  This is a no-new-reference assertion, not proof that every pre-existing
  reference in the complete project resolves.
- Paper-gap extraction: 4,641 citations, 4,043 unique heads; exit 0. This ran
  without `--check` and therefore is not compiled checkdecls verification.
- `prospective-tag-check.json`: all 222 changed/new tags exist in a source-only
  declaration index of external 592a plus the four b2 shared owner files and
  QIC729. It uses the repository's `collect_lean_decls` parser. This explicitly
  prospective index is not a coherent integrated proof tree and was not built;
  it verifies names only, not the migrated theorem signatures or proofs.
  The QIC source directory is an archive, not a Git checkout; all 1,683 Lean
  file blob hashes were independently matched against the exact 72942858 Git
  tree in the existing QIC object database, with zero mismatches.
- Actual staged-tree `blueprint_lean_sync.py --ci`: **failed**, exit 1, with
  976 missing declarations (975 carrying leanok), zero duplicate tags and no
  lean_decls list discrepancies. The b2 consumers remain unmigrated and exact
  dependency source checkouts are absent from this isolated worktree. The
  original log/report remain at `/tmp/interaction-docs-staged-sync.log` and
  `/tmp/interaction-docs-staged-sync.json`; hashes and counts are recorded in
  `staged-sync-summary.json`. No passing full synchronization is claimed.
- Production, scripts (including all five fixtures), pin and Lean options have
  zero diff from b2. No Lean build, strict elaboration, PDF/web build, cold
  dependency build, push, PR update or merge was performed.

## Remaining integration gates

Apply this documentation change only alongside the independently reviewed MPS,
PEPS and shared-owner migrations. Recheck all changed tags against that actual
head, re-run full source synchronization with exact dependency sources, compiled
checkdecls and appropriate Blueprint/PDF checks. Retain all five migrated
fixtures and verify owner-triggered CI selection plus exact-pin elaboration.
A second reviewer must assess these 34 file deltas and any later signature drift.
