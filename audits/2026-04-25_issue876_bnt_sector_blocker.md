# Issue #876 / PR #882 current-main audit (2026-04-25)

## What was checked

- `gh issue view 876`
- `gh pr view 882 --json mergeable,mergeStateStatus,reviewDecision,comments,headRefName`
- `origin/main` after the merge of PR #886 and the later Gap §1 API PRs.
- PR #882 head `f3df1df5` on branch
  `claude/issue-876-formalizationmpscanonicalform-construct-general-bnt-sector`.

## Decision

PR #882 should not be force-rebased as-is.  Its main Lean contribution used the
name `MPSTensor.HasBNTSectorData` for a basis-level package of positive bond
dimension, TP/left-canonical normalization, irreducibility, and primitive
transfer maps.  Current `main` already defines `MPSTensor.HasBNTSectorData` in
`TNLean/MPS/FundamentalTheorem/SectorDecomposition.lean` as the actual
basis-of-normal-tensors hypothesis consumed by the sector comparison layer:

eventual linear independence of the basis MPV states.

Those are different mathematical predicates.  Replaying #882 would either
reintroduce a conflicting name or silently weaken the post-#886 API.

## Precise blocker

The granular construction "one sector basis tensor per input block" is a useful
packaging step, but it does not prove the current `HasBNTSectorData` predicate.
TP + primitive + irreducible block data gives normal building blocks; it does
not by itself prove that the MPV state family is eventually linearly independent.
That is exactly the paper-level basis-of-normal-tensors construction: dependent
or gauge-phase-equivalent normal tensors must be identified/collapsed, and the
remaining basis must be proved linearly independent for all sufficiently large
system sizes.

So the old PR's target theorem is only coherent after adding an explicit BNT
linear-independence hypothesis, or after proving the missing one-sided BNT
construction theorem that produces such a basis from the blocked data.

## Replacement branch contribution

The replacement branch adds the small post-#886 adapter that is actually true:

- `MPSTensor.trivialSectorDecomp`
- `MPSTensor.sameMPV₂_trivialSectorDecomp`
- `MPSTensor.exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_of_linearIndependent`

The last theorem has the old TP/primitive/irreducible inputs but also requires

a supplied eventual-linear-independence hypothesis
`∃ N0, ∀ N > N0, LinearIndependent ℂ (fun k => mpvState (blocks k) N)`.
It then packages the granular sector decomposition and discharges the current
`HasBNTSectorData` by exactly that hypothesis.  This is not a closure of #876;
it is the clean adapter that future real BNT construction can feed.

## Remaining #876 theorem

A full solution of #876 still needs a theorem constructing a genuine BNT basis
from the blocked TP-primitive output.  Informally, it must:

1. group/collapse gauge-phase-equivalent normal tensors, absorbing phases into
   sector weights;
2. retain multiple distinct basis tensors even when their coefficient moduli are
   equal;
3. prove eventual linear independence of the resulting basis MPV states;
4. return a `SectorDecomposition` whose `HasBNTSectorData` is the current
   post-#886 linear-independence predicate.

Until that theorem exists, #860 and #877 should continue to treat the one-sided
BNT sector pair as a hypothesis, as in
`fundamentalTheorem_after_blocking_1606_sector_of_bntPair_matched`.
