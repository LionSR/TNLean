# Retirement of the pre-Condition-C1 BNT direct-sum selector span

This audit records the removal of the unsuffixed root of the BNT direct-sum
selector ladder in `TNLean/MPS/BNT/DirectSumSelectors.lean`. It is the audit
note required by `docs/project_conventions.md` §Style for removals under the
pass-through exception: the removed declaration is named below together with
the surviving declaration that supersedes it. No compatibility alias is
provided.

## Removed declaration and its replacement

| Removed | Replacement |
|---|---|
| `MPSTensor.wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors` | `MPSTensor.wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors_c1` |

Net Lean line delta: −25 lines, all in
`TNLean/MPS/BNT/DirectSumSelectors.lean`.

## Why it was stranded

`docs/audits/2026-08-26_mps_chain_bnt_zero_reference_and_pass_through_cleanup.md`
removed the existential wrapper
`MPSTensor.exists_wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors`
and named this root as the inline replacement at the use site. No use site
survived that migration, so the root has been referenced by nothing since.

The companion retirement
`docs/audits/2026-08-26_pre_condition_c1_bnt_route_retirement.md` cut the same
pre-Condition-C1 branch inside `TNLean/MPS/ParentHamiltonian/`, but it predates
the creation of `TNLean/MPS/BNT/DirectSumSelectors.lean` by PR #7199, so the
selector-span root in the new module was outside its reach.

The single surviving consumer of the ladder,
`TNLean/MPS/ParentHamiltonian/BNTBlockIntersection.lean:79`, calls the `_c1`
rung.

## What the replacement does not cover

The `_c1` rung is not a strict generalization of the removed root. The root
takes `hBlk : ∀ k, Kraus.IsNBlkInjective (A k) L` together with `hL : 1 < L`;
the `_c1` rung takes block injectivity at `L₀`, at `L₀ + 1`, and at
`3 (L₀ + 1)`, with `hL₀ : 0 < L₀`. Block injectivity at length `L` does not
supply block injectivity at `L - 1`, so instantiating `L₀ := L - 1` is not
available and the length-`L` branch is dropped rather than subsumed.

The branch is safe to drop: it had no consumer, carried no blueprint `\lean{}`
tag, and its two paper-gap citations were repointed to the `_c1` rung (see
below).

## Deletion closure

The closure stops at the root. Its callee
`MPSTensor.hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv`
(`TNLean/MPS/BNT/DirectSumSelectors.lean`) stays live: it is used by
`TNLean/MPS/ParentHamiltonian/BNTBlockIntersection.lean:569` and is cited at
`docs/paper-gaps/pgvwc07_direct_sum_input.tex:236,280`. The file-level
`variable {d L : ℕ}` is retained for the same reason.

## Repointed citations

Two `\leanid` citations in `docs/paper-gaps/pgvwc07_direct_sum_input.tex` named
the removed root and now name the `_c1` rung:

- line 238, in the footnote on the selector datum and the finite direct-sum
  span. The following line, which read "and their Condition-C1 variants in",
  now reads "all in": after the repoint, the earlier phrasing would have
  duplicated the citation it introduced.
- line 281, in the footnote on the downstream consumers of the direct-sum
  input.

`\leanid` in `docs/paper-gaps/` is a formatting macro; no script validates it,
so these edits are documentation accuracy rather than a build gate.

## A historical note left unedited

`docs/audits/2026-08-26_mps_chain_bnt_zero_reference_and_pass_through_cleanup.md:22`
now names a declaration that no longer exists. That line is a historical
record of what the earlier pass did, and it is left unedited; this note is the
record that its named replacement has since been retired in turn.

## Verification

- `lake build` completes successfully at the repository root with the package
  lean options; no new error or linter warning on any touched file.
- `python3 scripts/check_forbidden_lean_tokens.py` is clean.
- `leanblueprint checkdecls` passes; no blueprint `\lean{...}` tag cited the
  removed declaration.

## Ledger

This is an evidence update to open ledger entry S2
(`docs/proof_debt_ledger.md`, issue #4564), not a new entry.
