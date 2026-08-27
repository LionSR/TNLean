# Deletion of the pre-Condition-C1 BNT direct-sum selector span

This audit records the direct deletion of the unsuffixed root of the BNT
direct-sum selector ladder from
`TNLean/MPS/BNT/DirectSumSelectors.lean`. Current code uses the surviving
Condition-C1 declaration named below.

## Removed declaration and its replacement

| Removed | Replacement |
|---|---|
| `MPSTensor.wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors` | `MPSTensor.wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors_c1` |

The theorem and its deprecation attribute were removed. TNLean does not promise
public Lean API compatibility, so a declaration with no current consumer is not
retained solely as a deprecated compatibility theorem.

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

## Scope of the replacement

The `_c1` rung is not a strict generalization of the removed root. The root took
`hBlk : ∀ k, Kraus.IsNBlkInjective (A k) L` together with `hL : 1 < L`; the
`_c1` rung takes block injectivity at `L₀`, at `L₀ + 1`, and at
`3 (L₀ + 1)`, with `hL₀ : 0 < L₀`. Block injectivity at length `L` does not
supply block injectivity at `L - 1`, so instantiating `L₀ := L - 1` is not
available.

That distinction does not justify retaining a zero-reference theorem under the
maintainer's no-public-API-compatibility policy. The removed branch had no
current consumer and carried no blueprint `\lean{}` tag.

## Dependency closure

Only the zero-reference root is deleted. Its callee
`MPSTensor.hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv`
(`TNLean/MPS/BNT/DirectSumSelectors.lean`) stays live: it is used by
`TNLean/MPS/ParentHamiltonian/BNTBlockIntersection.lean:569` and is cited at
`docs/paper-gaps/pgvwc07_direct_sum_input.tex:236,280`. Other declarations in
the file also use the file-level parameter `L`, so that parameter remains.

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
names the theorem removed here. That line remains a historical record of what
the earlier pass did; this note records its subsequent deletion.

## Verification

- The affected Lean module compiles with the package Lean options; no new error
  or linter warning is introduced.
- No blueprint `\lean{...}` tag requires the removed declaration.
- Repository searches find no remaining Lean declaration or consumer under the
  removed name; only historical audit references remain.

## Ledger

This is an evidence update to open ledger entry S2
(`docs/proof_debt_ledger.md`, issue #4564), not a new entry.
