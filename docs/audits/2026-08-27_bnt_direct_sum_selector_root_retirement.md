# Retirement of the pre-Condition-C1 BNT direct-sum selector span

This audit records the retirement from active use of the unsuffixed root of the
BNT direct-sum selector ladder in `TNLean/MPS/BNT/DirectSumSelectors.lean`. The
declaration is retained, with its exact original statement and proof, as a
deprecated compatibility theorem; new code should use the surviving
Condition-C1 declaration named below.

## Deprecated declaration and its replacement

| Deprecated compatibility theorem | Replacement |
|---|---|
| `MPSTensor.wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors` | `MPSTensor.wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors_c1` |

The original 25-line theorem body is retained in
`TNLean/MPS/BNT/DirectSumSelectors.lean` with a deprecation attribute.

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

The `_c1` rung is not a strict generalization of the deprecated root. The root
takes `hBlk : ∀ k, Kraus.IsNBlkInjective (A k) L` together with `hL : 1 < L`;
the `_c1` rung takes block injectivity at `L₀`, at `L₀ + 1`, and at
`3 (L₀ + 1)`, with `hL₀ : 0 < L₀`. Block injectivity at length `L` does not
supply block injectivity at `L - 1`, so instantiating `L₀ := L - 1` is not
available, so the length-`L` branch is retained for compatibility rather than
subsumed by the preferred theorem.

The branch has no current consumer and carries no blueprint `\lean{}` tag, but
it is retained for source compatibility. Its two paper-gap citations remain
repointed to the `_c1` rung so current documentation directs new code to the
preferred theorem (see below).

## Retention and dependency closure

No deletion closure is taken because the root remains as a deprecated
compatibility theorem. Its callee
`MPSTensor.hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv`
(`TNLean/MPS/BNT/DirectSumSelectors.lean`) stays live: it is used by
`TNLean/MPS/ParentHamiltonian/BNTBlockIntersection.lean:569` and is cited at
`docs/paper-gaps/pgvwc07_direct_sum_input.tex:236,280`. The file-level
`variable {d L : ℕ}` is retained for the same reason.

## Repointed citations

Two `\leanid` citations in `docs/paper-gaps/pgvwc07_direct_sum_input.tex` named
the unsuffixed root and now name the preferred `_c1` rung:

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
names the compatibility theorem retained here. That line remains a historical
record of what the earlier pass did; this note records that the named replacement
is now deprecated rather than deleted.

## Verification

- The affected Lean module compiles with the package lean options; no new error
  or linter warning is introduced.
- No blueprint `\lean{...}` tag requires the deprecated declaration.

## Ledger

This is an evidence update to open ledger entry S2
(`docs/proof_debt_ledger.md`, issue #4564), not a new entry.
