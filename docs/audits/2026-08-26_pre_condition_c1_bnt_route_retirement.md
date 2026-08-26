# Retirement of the pre-Condition-C1 BNT block-diagonal route

This audit records the removals made when the pre-Condition-C1 branch of the
BNT block-diagonal parent-Hamiltonian development was retired. It is the audit
note required by `docs/project_conventions.md` §Style for removals under the
pass-through exception: every removed declaration is named below together with
the surviving declaration that supersedes it. No compatibility alias is
provided.

## What was retired

The block-diagonal route in `TNLean/MPS/ParentHamiltonian/` was developed twice.
The earlier branch assumes a one-site injectivity hypothesis `hInj` together
with `1 < L`, and reaches the simultaneous product span at the length
`L + (r - 1) * (L + (L + L))`. The later branch (`_c1`) replaces both by the
single hypothesis that each block is injective at a common positive length
`L₀`, and the sharp branch (`_c1_pgvwc07`) reaches the source bound of
PGVWC07, Theorem 12.

The earlier branch had no consumer outside itself: the thirteen declarations
below form a closed subgraph, referenced only by one another. Each was checked
by name across `TNLean/` (excluding `Archive/`), `blueprint/src/`, `docs/`,
and `scripts/`, and the deletion was confirmed by a full `lake build`.

`docs/audits/2026-08-04_issue_status_audit.md:275` already classified the
residue in `BNTBlockIntersection.lean` as deletable.

## Removed declarations and their replacements

In `TNLean/MPS/ParentHamiltonian/BNTBlockIntersection.lean`:

| Removed | Replacement |
|---|---|
| `MPSTensor.pgvwc07_iSup_restriction_intersection_of_bnt_directSum_selectors` | `MPSTensor.pgvwc07_iSup_restriction_intersection_of_bnt_directSum_selectors_c1` |
| `MPSTensor.wordTupleSpanTop_of_ge_of_bnt_directSum_unital` | `MPSTensor.wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1` |
| `MPSTensor.groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital` | `MPSTensor.groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1` |
| `MPSTensor.pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital` | `MPSTensor.pgvwc07_iSup_restriction_intersection_of_ge_of_bnt_directSum_unital_c1` |
| `MPSTensor.pgvwc07_directSum_restriction_intersection_of_ge_of_bnt_directSum_unital` | `MPSTensor.pgvwc07_directSum_restriction_intersection_of_ge_of_bnt_directSum_unital_c1` |
| `MPSTensor.pgvwc07_iSup_restriction_intersection_eventually_of_bnt_directSum_unital` | `MPSTensor.pgvwc07_iSup_restriction_intersection_eventually_of_bnt_directSum_unital_c1` |

In `TNLean/MPS/ParentHamiltonian/BNTBlockDiagonalChain.lean`:

| Removed | Replacement |
|---|---|
| `MPSTensor.chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace_of_ge_of_bnt_directSum_unital` | `MPSTensor.chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace_of_ge_of_bnt_directSum_unital_c1` |
| `MPSTensor.chainGroundSpace_toTensorFromBlocks_le_iSup_and_iSupIndep_of_bnt_unital` | `MPSTensor.chainGroundSpace_toTensorFromBlocks_le_iSup_and_iSupIndep_of_bnt_unital_c1` |
| `MPSTensor.chainGroundSpace_toTensorFromBlocks_two_inclusions_and_iSupIndep_of_bnt_unital` | `MPSTensor.chainGroundSpace_toTensorFromBlocks_two_inclusions_and_iSupIndep_of_bnt_unital_c1` |

In `TNLean/MPS/ParentHamiltonian/BNTBlockDiagonalBoundaryClosing.lean`:

| Removed | Replacement |
|---|---|
| `MPSTensor.exists_blockDiagonal_boundary_chainGroundSpace_of_global_cut_bnt_c1` | `MPSTensor.exists_blockDiagonal_boundary_chainGroundSpace_of_global_cut_bnt_c1_pgvwc07` |
| `MPSTensor.chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_global_cut_bnt_c1` | `MPSTensor.chainGroundSpace_toTensorFromBlocks_eq_iSup_and_iSupIndep_of_global_cut_bnt_c1_pgvwc07` |
| `MPSTensor.chainGroundSpace_toTensorFromBlocks_eq_iSup_of_global_cut_bnt_c1` | `MPSTensor.chainGroundSpace_toTensorFromBlocks_eq_iSup_of_global_cut_bnt_c1_pgvwc07` |
| `MPSTensor.ker_parentHamiltonian_toTensorFromBlocks_le_bntMPSVectorSpan_of_global_cut_bnt_c1` | `MPSTensor.ker_parentHamiltonian_toTensorFromBlocks_le_bntMPSVectorSpan_of_global_cut_bnt_c1_pgvwc07` |

## What the replacement does not cover

For the four `BNTBlockDiagonalBoundaryClosing` removals the survivor is not a
strict generalization. The `_c1_pgvwc07` form drops the hypotheses `hN`, `hL`,
and `hLN` and adds `hr : 2 ≤ r`, so the case of a single block is dropped
rather than subsumed. That case is the degenerate one-block reading of the
block-diagonal statement; it had no consumer, no blueprint `\lean{}` tag, and
no paper-gap citation, and the source theorem (PGVWC07, Theorem 12) is stated
for at least two blocks.

The cut also removes two in-source "This earlier variant is retained ..."
notes in `BNTBlockDiagonalBoundaryClosing.lean`, which recorded the soft
retention that this pass supersedes.

## Marker consolidation

Three declaration-level restriction markers restated their own module
docstring marker verbatim and were removed:

- `BNTBlockIntersection.lean`, on
  `MPSTensor.wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1_pgvwc07`. The
  module marker now names the three declarations it covers and states that the
  `_of_dualFixedPoint` variants, which assume the source dual fixed-point
  equation, are not covered.
- `BNTBlockDiagonalTraceDecomposition.lean`, on
  `MPSTensor.exists_blockDiagonal_boundary_chainGroundSpace_of_trace_decomposition_bnt_c1`.
  The module marker already scopes by hypothesis and covers it.

The declaration-level marker on
`MPSTensor.exists_blockDiagonal_boundary_chainGroundSpace_of_short_crossing_span_bnt_c1`
in `BNTBlockDiagonalPGVWCComparison.lean` was **retained**: it states the
`hShortSpan` restriction, which is strictly weaker than the module's crossing-span
marker, so folding it into the module marker would over-claim.

## Verification

- `lake build` completes successfully with the package lean options; no new
  error or linter warning on any touched file.
- `rg -n "sorry|axiom"` is clean on all four touched files.
- `leanblueprint checkdecls` passes; no blueprint `\lean{...}` tag cited any
  removed declaration.
- Net Lean line delta: −528 (−219 `BNTBlockIntersection.lean`, −136
  `BNTBlockDiagonalChain.lean`, −157 `BNTBlockDiagonalBoundaryClosing.lean`,
  −16 `BNTBlockDiagonalTraceDecomposition.lean`).

## Ledger

This is an evidence update to open ledger entry S2
(`docs/proof_debt_ledger.md`, issue #4564), not a new entry: the
`BNTBlockIntersection.lean` residue it names is exactly the concentration
retired here.
