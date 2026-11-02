# Non-QCA triage refresh, 2 November 2026

Published snapshot: **2026-11-02 07:46 UTC**. Inspected main: `94be858590a273e03d037b39210302a4173b2668`.
Current captured inventory: **157 open issues and 6 open PRs**.
QCA/MPU and related mixed programs remain excluded. No source build,
elaboration, PR merge or unpublished-proof import was performed.

## Latest outcome

- Of the previous 35 audited mathematical PRs, **30 merged**, **one closed
  without merging** (#10426), and **four remain open**. Closure without merge
  is recorded separately from integration.
- QICLean #1009/#1010/#1011/#1013 are all merged. Current TNLean main
  selects accepted QICLean `ba01733099b5a18bed5c9bfb62f95f175b4c9b57`.
- Closed **#9836 for the corrected invariant-line entropy-bootstrap result**,
  after accepted-source, exact-head CI, pin and review checks. The printed
  false formula and degenerate-space distinction are preserved.
- Correctness issues **#10483 and #10489 remain open and unchanged on main**.
- New #10497 was scoped to the character-covariant endpoint extension; the
  several-independent-block target cannot be attributed to the injective,
  unique-ground-line source statement. New #10507 is helper ownership work.

## The four remaining mathematical PRs

CI here is for the listed exact head, not a proof of current-main readiness.

| PR | Exact head | Actual declared base | Current PR CI | Remaining gate |
|---|---|---|---|
| [#10248](https://github.com/LionSR/TNLean/pull/10248) feat(MPS/AreaLaw): construct physical DG improving families | `99408b81b` | main at `94be85859` | No current checks | Actual-base conflict; reconcile candidate pin and run combined CI |
| [#10250](https://github.com/LionSR/TNLean/pull/10250) feat(MPS/AreaLaw): bootstrap physical ground spaces at every accuracy | `fbafb1fa8` | #10248 at `99408b81b` | No current checks | Open parent and candidate pin; combined-main validation remains |
| [#10254](https://github.com/LionSR/TNLean/pull/10254) feat(Lattice): product forms for varying local dimensions and Trotter active indices | `ce497c351` | main at `94be85859` | No current checks | Actual-base conflict; assess surviving/redundant source delta and run CI |
| [#10256](https://github.com/LionSR/TNLean/pull/10256) feat(MPS/AreaLaw): bound regional entropy in the full physical ground space | `64f978f35` | #10250 at `fbafb1fa8` | Passing | Open parent and candidate pin; combined-main validation remains |

The declared-parent merges for #10250 and #10256 are clean. Their integrations
against main still conflict, so the clean parent checks do not clear the stack.
Only #10248 and #10254 carry an actual-declared-base conflict label. The
next source step is to reconcile **#10248 → #10250 → #10256** with the accepted
main/pin, and separately review #10254; current child CI is not a substitute
for acceptance of the combined result. No current review threads are unresolved
on these four PRs.

Two other PRs remain open:

| PR | Captured status | Scope |
|---|---|---|
| [#10495](https://github.com/LionSR/TNLean/pull/10495) | Prior head `61639c00f` passed CI and was approved. This new audit changes its head and needs its own CI/review. | Documentation delivery; no autonomous merge. |
| [#10246](https://github.com/LionSR/TNLean/pull/10246) | Current head `1bbf2e57b` has a completed build failure and a main conflict. | Coordinated Mathlib v4.36.0-rc1 upgrade; reported but not mutated in this pass. Main still uses Lean v4.35.0-rc3. |

## Corrected pin comparisons

For GitHub `compare/<candidate>...<accepted>`, `behind_by` counts candidate-only
commits; `ahead_by` counts accepted-only commits. The earlier 30 October table
reversed those columns and is corrected in this change. The divergent-branch
classification is unchanged. Counts concern the commit graph, not a number of
missing or unaccepted mathematical proofs.

| PR | Selected candidate | Candidate-only | Accepted-main-only |
|---|---|---:|---:|
| [#10248](https://github.com/LionSR/TNLean/pull/10248) | `23d79b77661607507875d4d0527eeab4e041542c` | 10 | 42 |
| [#10250](https://github.com/LionSR/TNLean/pull/10250) | `3d15bc78a7a20531e836001cbe91dcd27b6d24b9` | 17 | 42 |
| [#10256](https://github.com/LionSR/TNLean/pull/10256) | `62085f064eb4697595201227f09588eb83debda4` | 23 | 40 |

The accepted comparison endpoint is current QICLean main
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`. Required upstream results are
now merged: the active work is source/API reconciliation and a coherent accepted
selection. Preserve required results and the newer main baseline when merging.
The accepted ancestor used by #10254 is not an upstream-approval blocker.

## Accepted leaf and remaining mathematical boundaries

| Issue | Current disposition |
|---|---|
| [#9836](https://github.com/LionSR/TNLean/issues/9836) | **Completed, corrected invariant-line estimate.** QIC #1010 accepted head `d500e4182b381ef02fc4a13b47d3a29e804eed82`, merge `6dd18fd5`; all three mathematical blobs are unchanged at the current TN pin, exact run [41248899684](https://github.com/LionSR/QICLean/actions/runs/41248899684) passed and current reviews are clear. The general bound is `12 (1+log(μ⁻¹)/(-log δ)) log D`, with zero-shrinking/rank endpoints and accepted favorable/tail foundations. The false printed formula and Bell-vector record remain documented in QICLean; no arbitrary degenerate-space extension is claimed. |
| [#9838](https://github.com/LionSR/TNLean/issues/9838) / [#9839](https://github.com/LionSR/TNLean/issues/9839) | The actual original-vector FF and general entropy constructions are integrated. The sharper source rate without inverse-gap logarithms remains mathematical work; obsolete owner blockers were removed. |
| [#9840](https://github.com/LionSR/TNLean/issues/9840) | The integrated general approximation has the weaker logarithmic-length rate. The stronger FF `log(length)^(2/3)` schedule is still not derived by it. |
| [#9844](https://github.com/LionSR/TNLean/issues/9844) | The actual NN-chain residual/spectral/closeness capstone is integrated, at sufficient `t≥η+7` with the finite-window remainder. The expressly retained general bounded-interaction lattice target and corrected source/window scope remain open. Missing-upstream/owner wording was removed; do not duplicate the chain proof or claim the unrestricted printed cutoff. |
| [#10483](https://github.com/LionSR/TNLean/issues/10483) | Still open: the optional `PeriodicEqualCaseFT` family-to-tensor premise remains in the source. The reported unipotent counterexample matches those definitions; the multiplicity-bearing theorem and unconditional corollary remain unaffected. No unpublished Lean proof was imported. |
| [#10489](https://github.com/LionSR/TNLean/issues/10489) | Still open: the mixed damping theorems retain silent `[NeZero a] [NeZero b]` premises. Resolve source faithfulness or the dimension cases; no new marker/elimination was found on main. |
| [#10497](https://github.com/LionSR/TNLean/issues/10497) | Source-domain correction: SPC11 II.F is the injective/unique-ground-line case. Keep the character-covariant original-endpoint extension and justify admissible blocking/class transport. A degenerate several-block classification needs a separate source and permutation/stabilizer data. The accepted restricted #10341 theorem is credited. |
| [#10507](https://github.com/LionSR/TNLean/issues/10507) | Three generic Matrix/linear-map helpers remain in the asymmetric-FT proof module. This is source ownership/discoverability, not a proof defect; scout existing upstream APIs before choosing the new owner. |
| [#664](https://github.com/LionSR/TNLean/issues/664) | Reverse root existence remains its own proof obligation; none of these entropy/SPT integrations completes it. |

## Closed PR #10426: policy disposition, not integration

#10426 closed on 1 November without merging. Its head is not an ancestor
of main, and its thirteen-site counterexample module/blueprint apparatus is
absent from accepted main. The maintainer’s
[closing decision](https://github.com/LionSR/TNLean/pull/10426#issuecomment-6560365427)
rejects the degenerate-literal-reading apparatus under the convention policy.
It remains closed; this refresh neither restores it nor treats it as a pending
counterexample acceptance task. Four current review threads remain archived
on that closed PR.

Current `CanonicalArbitraryInteractionDegeneracy.lean` still takes
`BlocksNotGaugePhaseEquiv` separately. Any remaining alignment of the intended
projective-distinctness convention belongs in the definitions/source bookkeeping;
the rejected literal-reading apparatus is not a new mathematical obstruction.
#7684’s older “draft counterexample” prose was superseded, without inferring
completion of its separate short-chain/source-wording obligations.

## Merged review loose ends

Ten of the newly merged PRs retain **39 current unresolved review threads**.
They are not counted as open PRs or silently erased. Explicit existing follow-ups
remain the routing where available.

| Merged PR | Current unresolved threads | Follow-up / review |
|---|---:|---|
| [#10408](https://github.com/LionSR/TNLean/pull/10408) | 3 | [current review](https://github.com/LionSR/TNLean/pull/10408/files) |
| [#10411](https://github.com/LionSR/TNLean/pull/10411) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10411/files) |
| [#10414](https://github.com/LionSR/TNLean/pull/10414) | 5 | [current review](https://github.com/LionSR/TNLean/pull/10414/files) |
| [#10416](https://github.com/LionSR/TNLean/pull/10416) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10416/files) |
| [#10427](https://github.com/LionSR/TNLean/pull/10427) | 4 | [current review](https://github.com/LionSR/TNLean/pull/10427/files) |
| [#10432](https://github.com/LionSR/TNLean/pull/10432) | 5 | [current review](https://github.com/LionSR/TNLean/pull/10432/files) |
| [#10433](https://github.com/LionSR/TNLean/pull/10433) | 5 | [current review](https://github.com/LionSR/TNLean/pull/10433/files) |
| [#10434](https://github.com/LionSR/TNLean/pull/10434) | 3 | [current review](https://github.com/LionSR/TNLean/pull/10434/files) |
| [#10435](https://github.com/LionSR/TNLean/pull/10435) | 4 | [current review](https://github.com/LionSR/TNLean/pull/10435/files) |
| [#10436](https://github.com/LionSR/TNLean/pull/10436) | 8 | [current review](https://github.com/LionSR/TNLean/pull/10436/files) |

The broader source/acceptance checks did not establish new closures for #7936,
#6088, #10397, #9264 or #10493. Some documentation is fixed (#10492 is closed),
but #10491 remains open. Actual artifact/export acceptance, scoped prose and
the remaining formula displays are not inferred from merges or unrelated CI.
The tenkz containing-release gate #8351 is unchanged: the pinned `286d63f2`
still has no containing release in the refreshed tag inventory.

## Verification and history

Checked current GitHub states, exact-head PR CI, complete current review
threads, actual base refs/merge trees and selected source definitions/accepted
blob identities. Read back changed labels, bodies and the #9836 COMPLETED state.
The status pass is bounded; it is not a new proof audit of all open issues.

All local changes are Markdown. No local Lean, Lake, build, elaboration or
checkdecls ran. No PR was merged, no closed-policy PR was reopened, and QCA
work was left untouched.

Earlier snapshots: [31 October](2026-10-31_non_qca_triage.md) and
[30 October](2026-10-30_non_qca_triage.md). Their old workflow states are
historical; the corrected pin-comparison direction is stated explicitly above.
