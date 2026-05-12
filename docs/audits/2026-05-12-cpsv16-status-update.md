# CPSV16 §II FT Realignment Status Update

Update date: 2026-05-12

## What has been achieved

- The four proof-gap notes in this worktree now use equation-first formatting and
  do not present Lean declaration names as standalone displayed math blocks:
  - `docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`
  - `docs/paper-gaps/cpsv16_equalMPS_gauge_phase_gap.tex`
  - `docs/paper-gaps/cpsv16_fixed_block_cancellation.tex`
  - `docs/paper-gaps/cpsv16_nonzero_proportionality_reading.tex`
- The same four notes were regenerated to PDF in
  `docs/paper-gaps/*.pdf` for reading and review.
- The notes now use `\leanid{...}` consistently and keep `\leanid` as inline text
  in non-equation narration.
- The fixed-block gap note explicitly singles out the residual-span hypothesis
  used in CPSV16 Theorem II.1 and the remaining mismatch with the source
  Lemma `Lem1`.
- The normalization-note text records the mismatch between limit-at-infinity input
  and finite-length power-sum inputs in CPSV16 normalization handling.
- The nonzero-proportionality note records the projective interpretation used in
  contradiction branches and the difference between `ProportionalMPV2` and
  `NonzeroProportionalMPV2`.
- The overlap-decay audit file
  `docs/audits/2026-05-11-cpsv16-overlap-decay-faithfulness.md`
  remains the current faithfulness map for `equalMPS` components.

## What is currently difficult

- Rectangular recovery of dimensions (`equalMPS` source branch) remains not fully
  formalized. This is tracked by issue cluster `#1567` and remains a bottleneck for
  #1566.
- The full fixed-block cancellation argument in CPSV16 Theorem II.1 still requires a
  source-faithful elimination of the residual-span hypothesis. See issue `#1607`.
- Global BNT multiplicity comparison (`Lem:app_simple` reconstruction in
  multi-sector form) remains the missing algebraic link for #1559 and #1562.
- Stage C (`#1563`) still depends on the same fixed-block branch and nonzero
  scalar handling; unresolved sorries remain linked to that branch.
- Broader project audit work (`#1565`) still has to collect these dependencies into
  the current tracker and issue graph once GitHub-sync is available.

## Open issue tree and sub-issue relations

Parent: `#1559` — CPSV16 §II proportional/equal MPV theorem.

- Sub-issue `#1563` — Stage C NonzeroOverlap.lean sorrys.
- Sub-issue `#1566` — Stage F Corollary II.2 global gauge.
- Sub-issue `#1562` — multi-copy generalization (linked to `#1561`).
  - Sub-sub issue pointer: `#1561`.
- Sub-issue `#1567` — rectangular equalMPS dimension recovery.
  - Blocked by `#1566` because gauge extraction needs dimension recovery.
- Sub-issue `#1565` — project-wide faithfulness audit.
  - Runs in parallel and collects every residual mismatch by path.

Parent: `#1498` — non-periodic FT.

- Sub-issues in this subtree: `#1499`, `#1500`, `#1501`, `#1503`.

Parent: `#1539` — proportional/multiplicity wrappers.

- Relies on the same one-copy/per-sector restriction chain as `#1559`.

## Next steps

- Stabilize the proof-gap note chain in Blueprint declarations so every source statement
  in CPSV16 §II has a precise hypothesis map and no undeclared extra assumption.
- Resolve #1567 and feed it back into #1566/#1559.
- Remove temporary scope restrictions only when each parent statement is replaced by a
  strictly source-faithful version.
- Keep the tracker synchronized with one concrete evidence link for each closed item:
  issue reference, PR number, and file-level witness.
