# Non-QCA triage refresh, 31 October 2026

Published refresh: **2026-10-31 19:11 UTC**. Frozen inspected main: `1c7d75bf87b037ed9d1fdf7e376b64eb47789e6b`.
Inventory captured after this refresh's issue changes: **207 open issues and 49 open PRs**,
before opening the documentation PR for this audit. The audited open scope is
**84 issues and 35 PRs**. QCA/MPU and related mixed programs remain
with Erickson and were not modified.

## What changed

- The previous repository snapshot had 183 open issues and 103 open PRs.
  The initial Oct31 inventory had 210 issues and 49 PRs: many integrated PRs
  now have explicit follow-ups. This pass closed four accepted mathematical
  leaves and opened one bounded documentation follow-up.
- **39 previously open audited PRs have merged.** The new 22-PR parent-Hamiltonian
  train #10464 is included in the remaining queue; inclusion in a pending train
  does not close its constituents.
- Scoped CI: **13 passing, 19 incomplete and 3 failing**.
  Actual-base merge checks: **24 conflicting, 11 clean**. CI, review,
  conflicts and mathematical acceptance are separate gates.
- **35 merged PRs still have current unresolved review findings.**
  22 explicit open follow-ups are linked across 17 merged PRs, including the
  new original-chain formula-display task #10493. Merge does not erase this debt.
- New correctness priority **#10483** concerns a false optional periodic-gauge
  hypothesis. Its reported counterexample matches the current definitions;
  the accepted multiplicity-bearing theorem and unconditional symmetry
  corollary are unaffected. No unpublished Lean witness was imported.

## Source-backed closures

| Completed issue | Accepted source and evidence | Remaining boundary |
|---|---|---|
| [#7850](https://github.com/LionSR/TNLean/issues/7850) Trace-form reuse | Merged #10292, accepted head `73c47deec`; retired helpers/module absent, replacements and signature preservation documented; accepted build/web/PDF. | Broader architecture cleanup remains separate. |
| [#6086](https://github.com/LionSR/TNLean/issues/6086) OBC canonical form and rectangular freedom | Accepted train #10461 at `4f58b65c`, merged `3ff8a98e`; nine proof files match main, PGVWC07 Theorems 1–2 constructed from the source inputs; accepted build/web/PDF. | Half-chain documentation, reconstruction and uniqueness remain separate. |
| [#8268](https://github.com/LionSR/TNLean/issues/8268) Corrected string-order tracker | Merged #10282 at accepted `fe85423b`; final overlap entry ready and source/normalized identities explicit; accepted build/web/PDF. | The documented false printed quotation stays visible; unrelated SPT/higher-dimensional work was never part of this closure scope. |
| [#9837](https://github.com/LionSR/TNLean/issues/9837) Original-chain robustness | Merged #10371 at `7f2dcead`; actual regional normalization/clipping, half-gap and aligned-error conclusions derived from raw bonds; accepted build/web/PDF and unchanged proof files. | Two prose findings are explicitly tracked in [#10493](https://github.com/LionSR/TNLean/issues/10493) under #9831. Sharper rates are not discharged. |

No parent was closed merely because its children or PRs merged. #7936 and
 #6088 remain open as documentation/review work; #9264 still lacks demonstrated
real artifact/export acceptance. Selected closures were checked against full
source criteria; other broad frontiers below are carried forward rather than
presented as newly exhaustive mathematical audits.

## Next work

| Order | Items | Concrete next gate |
|---|---|---|
| 1 | [#10483](https://github.com/LionSR/TNLean/issues/10483) | Retire the false family-to-tensor gauge premise, or restate the optional route using literal block data. Preserve the accepted unconditional results. |
| 2 | [#10489](https://github.com/LionSR/TNLean/issues/10489) | Resolve the silent nonzero-dimension hypotheses against the actual source; do not assume a trace-one field that is absent. |
| 3 | [#10432](https://github.com/LionSR/TNLean/pull/10432) | Exact head `48beacd5` fails HardTruncationResidual at lines 109, 149, 189, 192 and 200. Repair those completed diagnostics and validate the actual residual construction. |
| 4 | [#10427](https://github.com/LionSR/TNLean/pull/10427) / [#10338](https://github.com/LionSR/TNLean/pull/10338) | Current failures remain in the pinned QIC pure-output proof and the SPT Gaussian/positive-ray stack. Use current heads and accepted parent changes. |
| 5 | [#10464](https://github.com/LionSR/TNLean/pull/10464) / [#10455](https://github.com/LionSR/TNLean/pull/10455) | Review the combined train evidence and overlapping changes; constituents stay open until integrated. Do not close a train without checking for unique code. |
| 6 | [#6088](https://github.com/LionSR/TNLean/issues/6088), [#7936](https://github.com/LionSR/TNLean/issues/7936), [#10491](https://github.com/LionSR/TNLean/issues/10491), [#10492](https://github.com/LionSR/TNLean/issues/10492), [#10493](https://github.com/LionSR/TNLean/issues/10493) | Complete the precise post-merge notation, citation, formula and helper-ownership tasks. They are not absent capstone proofs. |
| 7 | [#9839](https://github.com/LionSR/TNLean/issues/9839) / [#9840](https://github.com/LionSR/TNLean/issues/9840) / [#664](https://github.com/LionSR/TNLean/issues/664) | Sharper entropy/FF approximation rates and reverse root existence remain mathematical work. Their integrated weaker ingredients are not the missing source result. |

## Labels and dependency gates

The [next-work filter](https://github.com/LionSR/TNLean/issues?q=is%3Aopen%20label%3A%22priority%3A%20next%22) and the taxonomy in
[CONTRIBUTING](../CONTRIBUTING.md#triage-status-and-priority-labels) remain authoritative.
Only inert organizational labels were added. No proof-writing automation
control was added. Status counts overlap.

| Live queue | Issues | PRs |
|---|---:|---:|
| [status: needs-proof](https://github.com/LionSR/TNLean/issues?q=is%3Aopen%20label%3A%22status%3A%20needs-proof%22) | 19 | 0 |
| [status: scope-decision](https://github.com/LionSR/TNLean/issues?q=is%3Aopen%20label%3A%22status%3A%20scope-decision%22) | 17 | 0 |
| [status: needs-work](https://github.com/LionSR/TNLean/issues?q=is%3Aopen%20label%3A%22status%3A%20needs-work%22) | 36 | 0 |
| [status: validation-pending](https://github.com/LionSR/TNLean/issues?q=is%3Aopen%20label%3A%22status%3A%20validation-pending%22) | 27 | 0 |
| [status: blocked](https://github.com/LionSR/TNLean/issues?q=is%3Aopen%20label%3A%22status%3A%20blocked%22) | 7 | 24 |
| [status: ci-failing](https://github.com/LionSR/TNLean/issues?q=is%3Aopen%20label%3A%22status%3A%20ci-failing%22) | 0 | 3 |
| [status: needs-ci](https://github.com/LionSR/TNLean/issues?q=is%3Aopen%20label%3A%22status%3A%20needs-ci%22) | 0 | 19 |
| [status: conflicts](https://github.com/LionSR/TNLean/issues?q=is%3Aopen%20label%3A%22status%3A%20conflicts%22) | 0 | 24 |
| [status: review-changes](https://github.com/LionSR/TNLean/issues?q=is%3Aopen%20label%3A%22status%3A%20review-changes%22) | 0 | 9 |
| [status: needs-review](https://github.com/LionSR/TNLean/issues?q=is%3Aopen%20label%3A%22status%3A%20needs-review%22) | 0 | 6 |

- Removed six stale PR blockers after accepted-parent/pin checks: #10432,
  #10426, #10414, #10408, #10403 and #10326. Logical side prerequisites
  remain blockers even when GitHub retargets the branch to main.
- The #10399 and #10302 owners are integrated; their retired candidate pins
  are not current-main blockers. Current main selects accepted QICLean
  `5065f76a30f327d9f30014e7f72cc0e5515161d9`.
- #10248 still selects divergent candidate `23d79b77661607507875d4d0527eeab4e041542c`;
  its accepted-repin gate remains. QICLean #1009/#1010/#1011/#1013 remain
  open at the inspected heads.
- #9839/#9840 lost obsolete owner blockers but retain needs-proof: removing
  inverse-gap logarithms and obtaining the stronger FF log(length)^(2/3)
  rate are not consequences of the integrated weaker bounds.
- #8351 still needs a tenkz release containing the actual required pin
  `286d63f2`. The refreshed tag inventory still only has `tenkz-v0.7.1` at
  `2210cfd1`; no new containing release was inferred.
- New correctness issue #10483 is now a native child of the active roadmap
  #1809. The old periodic source tracker #619 was not reopened because its
  unaffected multiplicity-bearing and unconditional results remain accepted.

## Merged review loose ends

Current unresolved findings are retained below. Linked follow-up issues
are the work routing, not proof that every finding has already been fixed.

| Merged PR | Current unresolved threads | Open follow-ups / review |
|---|---:|---|
| [#10302](https://github.com/LionSR/TNLean/pull/10302) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10302#discussion_r4419947293) |
| [#10309](https://github.com/LionSR/TNLean/pull/10309) | 4 | [#10469](https://github.com/LionSR/TNLean/issues/10469) |
| [#10310](https://github.com/LionSR/TNLean/pull/10310) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10310#discussion_r4429945223) |
| [#10312](https://github.com/LionSR/TNLean/pull/10312) | 9 | [#10454](https://github.com/LionSR/TNLean/issues/10454) |
| [#10313](https://github.com/LionSR/TNLean/pull/10313) | 2 | [current review](https://github.com/LionSR/TNLean/pull/10313#discussion_r4430223709) |
| [#10314](https://github.com/LionSR/TNLean/pull/10314) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10314#discussion_r4430781624) |
| [#10316](https://github.com/LionSR/TNLean/pull/10316) | 4 | [current review](https://github.com/LionSR/TNLean/pull/10316#discussion_r4431203675) |
| [#10317](https://github.com/LionSR/TNLean/pull/10317) | 3 | [#10479](https://github.com/LionSR/TNLean/issues/10479) |
| [#10320](https://github.com/LionSR/TNLean/pull/10320) | 4 | [#10482](https://github.com/LionSR/TNLean/issues/10482) |
| [#10323](https://github.com/LionSR/TNLean/pull/10323) | 3 | [current review](https://github.com/LionSR/TNLean/pull/10323#discussion_r4432855977) |
| [#10324](https://github.com/LionSR/TNLean/pull/10324) | 4 | [current review](https://github.com/LionSR/TNLean/pull/10324#discussion_r4432669168) |
| [#10325](https://github.com/LionSR/TNLean/pull/10325) | 13 | [#10489](https://github.com/LionSR/TNLean/issues/10489), [#10488](https://github.com/LionSR/TNLean/issues/10488), [#10487](https://github.com/LionSR/TNLean/issues/10487) |
| [#10328](https://github.com/LionSR/TNLean/pull/10328) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10328#discussion_r4422746072) |
| [#10331](https://github.com/LionSR/TNLean/pull/10331) | 1 | [#10456](https://github.com/LionSR/TNLean/issues/10456) |
| [#10334](https://github.com/LionSR/TNLean/pull/10334) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10334#discussion_r4422942423) |
| [#10342](https://github.com/LionSR/TNLean/pull/10342) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10342#discussion_r4431117937) |
| [#10345](https://github.com/LionSR/TNLean/pull/10345) | 13 | [current review](https://github.com/LionSR/TNLean/pull/10345#discussion_r4431514816) |
| [#10350](https://github.com/LionSR/TNLean/pull/10350) | 6 | [current review](https://github.com/LionSR/TNLean/pull/10350#discussion_r4423404384) |
| [#10361](https://github.com/LionSR/TNLean/pull/10361) | 7 | [current review](https://github.com/LionSR/TNLean/pull/10361#discussion_r4429209799) |
| [#10369](https://github.com/LionSR/TNLean/pull/10369) | 2 | [#10478](https://github.com/LionSR/TNLean/issues/10478) |
| [#10371](https://github.com/LionSR/TNLean/pull/10371) | 2 | [#10481](https://github.com/LionSR/TNLean/issues/10481), [#10493](https://github.com/LionSR/TNLean/issues/10493) |
| [#10376](https://github.com/LionSR/TNLean/pull/10376) | 11 | [current review](https://github.com/LionSR/TNLean/pull/10376#discussion_r4431436087) |
| [#10387](https://github.com/LionSR/TNLean/pull/10387) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10387#discussion_r4426368937) |
| [#10390](https://github.com/LionSR/TNLean/pull/10390) | 4 | [current review](https://github.com/LionSR/TNLean/pull/10390#discussion_r4424534731) |
| [#10396](https://github.com/LionSR/TNLean/pull/10396) | 8 | [#10480](https://github.com/LionSR/TNLean/issues/10480) |
| [#10398](https://github.com/LionSR/TNLean/pull/10398) | 4 | [#10460](https://github.com/LionSR/TNLean/issues/10460) |
| [#10400](https://github.com/LionSR/TNLean/pull/10400) | 2 | [#10470](https://github.com/LionSR/TNLean/issues/10470) |
| [#10402](https://github.com/LionSR/TNLean/pull/10402) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10402#discussion_r4427724092) |
| [#10404](https://github.com/LionSR/TNLean/pull/10404) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10404#discussion_r4429532992) |
| [#10405](https://github.com/LionSR/TNLean/pull/10405) | 2 | [#10486](https://github.com/LionSR/TNLean/issues/10486), [#10485](https://github.com/LionSR/TNLean/issues/10485) |
| [#10407](https://github.com/LionSR/TNLean/pull/10407) | 8 | [#10490](https://github.com/LionSR/TNLean/issues/10490) |
| [#10419](https://github.com/LionSR/TNLean/pull/10419) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10419#discussion_r4424265351) |
| [#10424](https://github.com/LionSR/TNLean/pull/10424) | 3 | [current review](https://github.com/LionSR/TNLean/pull/10424#discussion_r4432228898) |
| [#10425](https://github.com/LionSR/TNLean/pull/10425) | 1 | [current review](https://github.com/LionSR/TNLean/pull/10425#discussion_r4423238123) |
| [#10429](https://github.com/LionSR/TNLean/pull/10429) | 2 | [#10473](https://github.com/LionSR/TNLean/issues/10473) |

## Open issue routing

Native sub-issues remain the hierarchy. New follow-ups were classified from
their concrete source/review requests. Older broad rows retain their frontier
unless a source-specific audit above established a different disposition.

| Issue | Native parent | Remaining-work labels | Next action |
|---|---|---|---|
| [#190](https://github.com/LionSR/TNLean/issues/190) Tracking: MPS parent-Hamiltonian theory (arXiv:2011.12127 §IV.C + FNW/Nachtergaele) | [#1809](https://github.com/LionSR/TNLean/issues/1809) | needs-proof, validation-pending | The canonical OBC leaf is complete. Review the remaining uniqueness/reconstruction and uncle trains, source-quantifier decisions and exact follow-ups separately. |
| [#622](https://github.com/LionSR/TNLean/issues/622) Tracking: p-refinement and p-divisibility in arXiv:1708.00029 Theorem 4.1 | [#1809](https://github.com/LionSR/TNLean/issues/1809) | needs-proof | Forward leaf #7762 is completed. Keep reverse root existence #664 open until its source-faithful root/rank argument or obstruction is settled. |
| [#664](https://github.com/LionSR/TNLean/issues/664) MPS/Periodic: compatible root Kraus-rank bound for Theorem 4.1 | [#622](https://github.com/LionSR/TNLean/issues/622) | needs-proof | Prove faithful root existence or document an actual obstruction; preserve source correction and do not reuse the refuted forward hypothesis. |
| [#2147](https://github.com/LionSR/TNLean/issues/2147) Tracking: completeness of the 1D SPT classification for injective MPS | [#8273](https://github.com/LionSR/TNLean/issues/8273) | scope-decision, validation-pending | The physical-gap ingredient is integrated. The remaining SPT stack and its exact-covariance source-domain boundary still need review; no unrestricted classification closure. |
| [#2947](https://github.com/LionSR/TNLean/issues/2947) Quantitative quantum Wielandt inequality and translation-invariant W-state bond-dimension lower bound | [#8014](https://github.com/LionSR/TNLean/issues/8014) | needs-proof | W-state blocking/prime-divisor owner #10429 is integrated. The full arbitrary-length/index result remains mathematical work; duplication cleanup is separately #10473. |
| [#4522](https://github.com/LionSR/TNLean/issues/4522) PEPS: region-parametrized insertion interface for the edge, region, and coarse machinery | [#4529](https://github.com/LionSR/TNLean/issues/4529) | needs-work | Owner(s) #10355 are now merged; review the remaining full source scope and current documentation follow-ups before closure. |
| [#4529](https://github.com/LionSR/TNLean/issues/4529) Tracking: proof-debt reduction | [#1809](https://github.com/LionSR/TNLean/issues/1809) | needs-work | Keep native ownership and bounded acceptance separate from debt counts; route excluded #10025 and #7845 to their owner. |
| [#5693](https://github.com/LionSR/TNLean/issues/5693) Move the blueprint's diagram equations into the tenkzeq scope | [#8621](https://github.com/LionSR/TNLean/issues/8621) | needs-work | Choose the tenkzequation wrapper/migration/equation-side audit design and coordinate diagram owners; generic documentation/CI work only, without sweeping MPU/QCA chapters. |
| [#6085](https://github.com/LionSR/TNLean/issues/6085) Tracking: PGVWC07 Matrix Product State Representations coverage | [#1809](https://github.com/LionSR/TNLean/issues/1809) | scope-decision, validation-pending | Canonical OBC leaf #6086 is completed. Keep half-chain documentation #6088, quadratic reconstruction #6089 and Theorem 9/11 obligations #7684 separate. |
| [#6088](https://github.com/LionSR/TNLean/issues/6088) Formalize the PGVWC07 half-chain interpretation of the dual fixed point | [#6085](https://github.com/LionSR/TNLean/issues/6085) | needs-work | The actual half-chain capstone is integrated. Complete the current normality/citation/notation/formula findings on merged #10342/#10345; avoid rebuilding the capstone. |
| [#6089](https://github.com/LionSR/TNLean/issues/6089) Formalize PGVWC07 quadratic reconstruction of the TI canonical form | [#6085](https://github.com/LionSR/TNLean/issues/6085) | scope-decision, validation-pending | The prescribed-window construction is written in still-open #10381/#10388. Reconcile actual-base conflicts and review the exact source scope before acceptance. |
| [#7681](https://github.com/LionSR/TNLean/issues/7681) Tracking: region parent Hamiltonians and two-dimensional ground spaces | [#190](https://github.com/LionSR/TNLean/issues/190) | scope-decision | Reconcile accepted graph framework and #7936 scope with #8271 global-source frontier before closure. |
| [#7684](https://github.com/LionSR/TNLean/issues/7684) Open-boundary uniqueness and degeneracy for arbitrary frustration-free local Hamiltonians | [#6085](https://github.com/LionSR/TNLean/issues/6085) | scope-decision, validation-pending | Theorem 9 uniqueness remains in unmerged #10422/train #10464; preserve its short-chain convention. Theorem 11 source interpretation and #10426 remain separate. |
| [#7685](https://github.com/LionSR/TNLean/issues/7685) Tracking: alternative Hamiltonians, product vacua with boundary states, and uncle Hamiltonians | [#190](https://github.com/LionSR/TNLean/issues/190) | validation-pending | Ground-space and several variational ingredients are integrated; the final gaplessness owner #10326 and current documentation/faithfulness follow-ups remain. |
| [#7936](https://github.com/LionSR/TNLean/issues/7936) Formalize physical-deformation ground-space correspondence for general-graph parent Hamiltonians | [#7681](https://github.com/LionSR/TNLean/issues/7681) | needs-work | The maintained proper-arc assembly is integrated. Address the current import-hygiene finding and stale source-gap note; retain the explicit full-ring/small-cycle conventions. |
| [#8271](https://github.com/LionSR/TNLean/issues/8271) Tracking: PEPS ground states, degeneracy and topology after Schuch, Cirac, and Pérez-García | [#1809](https://github.com/LionSR/TNLean/issues/1809) | needs-proof | Refresh #10364 to merged one-block status; retain both genuine source leaves and unaccepted recovery provenance. |
| [#8274](https://github.com/LionSR/TNLean/issues/8274) Tracking: quantum Wielandt inequality after Sanz, Pérez-García, Wolf, and Cirac | [#1809](https://github.com/LionSR/TNLean/issues/1809) | validation-pending | The index-comparison owners are integrated. Perform the remaining full source-coverage review, including literal-spectrum/irreducibility leaves, and citation follow-up #10468. |
| [#8351](https://github.com/LionSR/TNLean/issues/8351) Restore tenkz.toml pin to a tag once tenkz cuts a release | [#8621](https://github.com/LionSR/TNLean/issues/8621) | blocked | Verify exact containing release tag and feature/diagram compatibility before changing the pin; keep external-release gate rather than claiming missing Lean math. |
| [#8469](https://github.com/LionSR/TNLean/issues/8469) Formalize the non-normal case of transforming MPS in the same phase with a log-depth circuit | [#8620](https://github.com/LionSR/TNLean/issues/8620) | scope-decision | Resolve the intended source phase/selected-vector relation and derive justified coefficient transport. Do not invent compatible-seed hypotheses and call that the unrestricted theorem. |
| [#8620](https://github.com/LionSR/TNLean/issues/8620) Tracking: log-depth preparation of matrix product states | [#1809](https://github.com/LionSR/TNLean/issues/1809) | scope-decision | Keep tracker open for #8469 source interpretation; do not label the whole preparation infrastructure as missing. |
| [#8621](https://github.com/LionSR/TNLean/issues/8621) Tracking: CI and build maintenance | [#1809](https://github.com/LionSR/TNLean/issues/1809) | needs-work | Prioritize actual CI failures/conflicts, real artifact acceptance #9264, profiling #9961, the tenkz release gate and precise post-merge documentation tasks. |
| [#8622](https://github.com/LionSR/TNLean/issues/8622) Tracking: local channel conversions of matrix product states | [#1809](https://github.com/LionSR/TNLean/issues/1809) | scope-decision, validation-pending | Exact original-port owner #10424 is integrated. Approximate #10427 still fails on unaccepted QIC #1009; retain the independent adaptive-control and resource-scope decisions. |
| [#8640](https://github.com/LionSR/TNLean/issues/8640) Compare bounded enlarged-site channels with fixed-physical-qudit gate costs | [#8622](https://github.com/LionSR/TNLean/issues/8622) | scope-decision, validation-pending | The exact bounded original-port construction is integrated. Complete approximate #10427 acceptance and retain the source control/environment/resource distinctions. |
| [#8703](https://github.com/LionSR/TNLean/issues/8703) SCP10 6.13–6.14: flux paths, endpoint holonomy and local deformation | [#8271](https://github.com/LionSR/TNLean/issues/8271) | needs-proof, scope-decision | Choose the intended source geometry and prove the retained arbitrary-region/open-boundary and reduced-density generalizations; preserve winding/exterior caveats. |
| [#8885](https://github.com/LionSR/TNLean/issues/8885) Formalize the GVBS-to-faithful-minimal-generating-data reduction (Nachtergaele96, lines 1724–1738) | [#190](https://github.com/LionSR/TNLean/issues/190) | needs-proof | Develop source-faithful raw GVBS boundary-limit normalization/minimal representation; reuse accepted compression. Do not assume a fully-supported corner or conflate local support with original full boundary range. |
| [#8947](https://github.com/LionSR/TNLean/issues/8947) SCP10 §7D: full-lattice quantum-double parent Hamiltonian and T-to-K transport | [#8271](https://github.com/LionSR/TNLean/issues/8271) | needs-proof | Refresh stale draft wording and distinguish completed one-block renormalization from the global theorem; recover usable source when available but implement only genuine missing global classification. |
| [#9098](https://github.com/LionSR/TNLean/issues/9098) Relocate map_list_prod_eq_pow_mul_of_length_three to TNLean/Algebra/ once it gains a second consumer | [#190](https://github.com/LionSR/TNLean/issues/190) | scope-decision | Defer generic helper extraction until a real second consumer exists; current census has one call. |
| [#9264](https://github.com/LionSR/TNLean/issues/9264) Re-pin the coherent TN prerequisite baseline to a current main commit | [#8621](https://github.com/LionSR/TNLean/issues/8621) | validation-pending | Owner(s) #10298 are now merged; review the remaining full source scope and current documentation follow-ups before closure. |
| [#9547](https://github.com/LionSR/TNLean/issues/9547) Tracking: one-dimensional area law and matrix product state approximation | [#1809](https://github.com/LionSR/TNLean/issues/1809) | needs-work | The strip and snake mathematics is integrated and all 21 children are closed. Complete the missing strip-tail blueprint dependency and snake-grid notation correction; review links are listed above. |
| [#9809](https://github.com/LionSR/TNLean/issues/9809) Tracking: one-dimensional area law and ground-state approximation, comparison of techniques | [#1809](https://github.com/LionSR/TNLean/issues/1809) | needs-proof, validation-pending | Canonical, normalization, rank and several construction leaves are integrated. Keep six-paper source rates, complexity and remaining physical truncation/FF integration distinct. |
| [#9823](https://github.com/LionSR/TNLean/issues/9823) Viable sets for the ground state of a gapped chain after Landau, Vazirani and Vidick | [#9832](https://github.com/LionSR/TNLean/issues/9832) | needs-proof, validation-pending | Owner(s) #10362 are now merged; review the remaining full source scope and current documentation follow-ups before closure. |
| [#9828](https://github.com/LionSR/TNLean/issues/9828) Tracking: local solution of gapped Hamiltonians after Hastings | [#9809](https://github.com/LionSR/TNLean/issues/9809) | needs-work | Corrected Gaussian adoption is integrated. Complete #10397 follow-ups #10491/#10492; the old owner/pin blocker is discharged. |
| [#9831](https://github.com/LionSR/TNLean/issues/9831) Tracking: improved one-dimensional area law after Arad, Kitaev, Landau and Vazirani | [#9809](https://github.com/LionSR/TNLean/issues/9809) | needs-proof, validation-pending | Original-chain robustness #9837 is completed; its prose follow-up is #10493. Sharper rates and the unmerged FF stack remain separate. |
| [#9832](https://github.com/LionSR/TNLean/issues/9832) Tracking: polynomial-time ground states of gapped chains after Landau, Vazirani and Vidick | [#9809](https://github.com/LionSR/TNLean/issues/9809) | validation-pending | Owner(s) #10362 are now merged; review the remaining full source scope and current documentation follow-ups before closure. |
| [#9833](https://github.com/LionSR/TNLean/issues/9833) Tracking: rigorous renormalization-group algorithm after Arad, Landau, Vazirani and Vidick | [#9809](https://github.com/LionSR/TNLean/issues/9809) | needs-proof, validation-pending | Corrected FF and several physical ingredients are integrated. Retain the corrected-rank disposition #9849, open truncation #10432/#10433, and algorithm/LD/MPO obligations. |
| [#9836](https://github.com/LionSR/TNLean/issues/9836) Approximate ground-state projectors with a good shrinking-to-growth tradeoff give an area law | [#9831](https://github.com/LionSR/TNLean/issues/9831) | blocked, validation-pending | Track QIC #1010 corrected general estimate acceptance/pin; favorable corollary and arbitrary rank-tail summation already accepted independently. |
| [#9838](https://github.com/LionSR/TNLean/issues/9838) Chebyshev projector of a truncated chain Hamiltonian without the detectability lemma | [#9831](https://github.com/LionSR/TNLean/issues/9831) | blocked, needs-proof | General rank/normalization ingredients are accepted. The written original-vector FF stack remains open; sharper inverse-gap-log removal is independent mathematics. |
| [#9839](https://github.com/LionSR/TNLean/issues/9839) Area law of order log cubed of the local dimension over the gap for gapped chains | [#9831](https://github.com/LionSR/TNLean/issues/9831) | needs-proof | The general entropy owner is integrated. Prove the sharper printed rate without inverse-gap logarithms; this is not an unaccepted-owner/pin blocker. |
| [#9840](https://github.com/LionSR/TNLean/issues/9840) Sub-polynomial bond dimension for matrix product state approximation of gapped chains | [#9831](https://github.com/LionSR/TNLean/issues/9831) | needs-proof | The general approximation owner is integrated. The stronger FF log(length)^(2/3) rate is not implied by its general log(length)^(3/4) rate; retain this mathematical obligation. |
| [#9844](https://github.com/LionSR/TNLean/issues/9844) Hard truncation and closeness of low-energy subspaces | [#9833](https://github.com/LionSR/TNLean/issues/9833) | blocked, validation-pending | Repair exact-head residual diagnostics in #10432, then validate #10433 with QIC #1011/#1013 and coherent pins. The counterexample and window-note correction are already merged. |
| [#9845](https://github.com/LionSR/TNLean/issues/9845) Chebyshev spectral projector at two cuts and existence of good projectors | [#9833](https://github.com/LionSR/TNLean/issues/9833) | blocked, needs-proof | QIC #977 is merged. Reconcile the divergent #10248 candidate pin and validate the actual DG stack #10248/#10250/#10256 before integration. |
| [#9846](https://github.com/LionSR/TNLean/issues/9846) Area laws for degenerate ground spaces and for low-density low-energy spaces of chains | [#9833](https://github.com/LionSR/TNLean/issues/9833) | blocked, needs-proof | QIC #977 is merged. The actual DG stack remains open with a divergent candidate-pin gate; separate its proof from full runtime/algorithmic conclusions. |
| [#9847](https://github.com/LionSR/TNLean/issues/9847) Soft truncation and the matrix product operator of the truncated cluster expansion | [#9833](https://github.com/LionSR/TNLean/issues/9833) | needs-proof | Split corrected analytic chain estimate, explicit cluster MPO tensor, and efficient approximation obligations. |
| [#9848](https://github.com/LionSR/TNLean/issues/9848) Merge tree of viable subspaces for low-energy states of chains | [#9833](https://github.com/LionSR/TNLean/issues/9833) | needs-proof | After accepted projector/bootstrap inputs, construct actual merge-tree viable subspaces and trimming/rank bookkeeping. |
| [#9849](https://github.com/LionSR/TNLean/issues/9849) Detectability lemma, its converse and the frustration-free truncated Hamiltonian | [#9833](https://github.com/LionSR/TNLean/issues/9833) | scope-decision | Owner(s) #10328 are now merged; review the remaining full source scope and current documentation follow-ups before closure. |
| [#9879](https://github.com/LionSR/TNLean/issues/9879) SPT phases: different cohomology classes cannot be joined by a gapped symmetric MPS path | [#2147](https://github.com/LionSR/TNLean/issues/2147) | scope-decision, validation-pending | The physical-gap ingredient is integrated; remaining SPT owner/CI and exact-covariance source-domain gates persist. |
| [#9881](https://github.com/LionSR/TNLean/issues/9881) Proof debt: zero-reference declarations, October 2026 scan | [#4529](https://github.com/LionSR/TNLean/issues/4529) | needs-work | Both earlier small deletion slices are integrated. Refresh the residual census when useful and assess mathematical roles individually; no blanket deletion verdict. |
| [#9961](https://github.com/LionSR/TNLean/issues/9961) Blueprint PDF build time in pull-request CI | [#8621](https://github.com/LionSR/TNLean/issues/8621) | needs-work | Measure actual pass/cache/chapter costs in an authorized hosted profiling run, then propose bounded mitigation; no need to recreate timeout fix. |
| [#9984](https://github.com/LionSR/TNLean/issues/9984) Stale package cache for the blueprint system dependencies | [#8621](https://github.com/LionSR/TNLean/issues/8621) | blocked | Review/integrate/release the upstream action fix on consumedv1, then observe real Ubuntu cache save/hit behavior; no cache deletion or TN proof rewrite. |
| [#10275](https://github.com/LionSR/TNLean/issues/10275) Wielandt: compare the two indices for every quantum channel | [#8274](https://github.com/LionSR/TNLean/issues/8274) | validation-pending | Review the linked implementation against the full issue acceptance criteria; preserve unproved source obligations. |
| [#10276](https://github.com/LionSR/TNLean/issues/10276) Wielandt: derive irreducibility from the literal peripheral-spectrum condition | [#8274](https://github.com/LionSR/TNLean/issues/8274) | validation-pending | Review the linked implementation against the full issue acceptance criteria; preserve unproved source obligations. |
| [#10277](https://github.com/LionSR/TNLean/issues/10277) Wielandt: embed primitive stochastic matrices and identify their exponents | [#8274](https://github.com/LionSR/TNLean/issues/8274) | validation-pending | The stochastic owner and QIC #987 are integrated on the accepted pin. Finish the source-coverage/acceptance review; do not retain the retired branch-pin blocker. |
| [#10278](https://github.com/LionSR/TNLean/issues/10278) Wielandt: compute the two indices of the three-Pauli channel | [#8274](https://github.com/LionSR/TNLean/issues/8274) | validation-pending | Review the linked implementation against the full issue acceptance criteria; preserve unproved source obligations. |
| [#10279](https://github.com/LionSR/TNLean/issues/10279) Wielandt: prove the cyclic-shift lower-bound example | [#8274](https://github.com/LionSR/TNLean/issues/8274) | validation-pending | Review the linked implementation against the full issue acceptance criteria; preserve unproved source obligations. |
| [#10280](https://github.com/LionSR/TNLean/issues/10280) Wielandt: ground-state bond-dimension dichotomy at prime lengths | [#8274](https://github.com/LionSR/TNLean/issues/8274) | scope-decision, validation-pending | Review the linked implementation against the full issue acceptance criteria; preserve unproved source obligations. |
| [#10285](https://github.com/LionSR/TNLean/issues/10285) Uncle Hamiltonians: identify the full periodic ground space | [#7685](https://github.com/LionSR/TNLean/issues/7685) | validation-pending | The periodic ground-space owner is integrated. Review full issue coverage and the explicit uncle blueprint follow-ups before closing; no missing-implementation claim follows from stale prose. |
| [#10286](https://github.com/LionSR/TNLean/issues/10286) Uncle Hamiltonians: prove generic finite-volume gaplessness | [#7685](https://github.com/LionSR/TNLean/issues/7685) | validation-pending | Several energy/overlap/Rayleigh ingredients are integrated. The final positive-eigenvalue/gaplessness capstone #10326 still needs acceptance/integration. |
| [#10386](https://github.com/LionSR/TNLean/issues/10386) Zero-momentum ground vectors at the short volumes in the Wielandt dichotomy | [#10280](https://github.com/LionSR/TNLean/issues/10280) | scope-decision, validation-pending | Review the linked implementation against the full issue acceptance criteria; preserve unproved source obligations. |
| [#10397](https://github.com/LionSR/TNLean/issues/10397) Adopt the corrected Gaussian commutator expansion for the Hastings variational bound | [#9828](https://github.com/LionSR/TNLean/issues/9828) | needs-work | The corrected commutator proof is integrated. Complete helper/sign-convention ownership #10491 and stale readiness tags #10492. |
| [#10439](https://github.com/LionSR/TNLean/issues/10439) Cite the source and the ground-energy paper gap in ch35_lvv_sampled_construction.tex | [#9832](https://github.com/LionSR/TNLean/issues/9832) | needs-work | The source and ground-energy note are cited; the requested trimming-radius citation is still missing. Complete that precise documentation placement. |
| [#10454](https://github.com/LionSR/TNLean/issues/10454) Fix blueprint tag/uses direction and display formatting in ch13_parent_hamiltonian_uncle.tex | [#7685](https://github.com/LionSR/TNLean/issues/7685) | needs-work | Owner(s) #10312 are now merged; review the remaining full source scope and current documentation follow-ups before closure. |
| [#10456](https://github.com/LionSR/TNLean/issues/10456) Extract shared posSemidef-gap repackaging tail from normalized_chain_robustness and its inverse-gap-cutoff sibling | [#9831](https://github.com/LionSR/TNLean/issues/9831) | needs-work | Extract the shared positive-semidefinite gap-repackaging tail from the two accepted robustness proofs, update both callers and the tactic ledger; no new theorem is needed. |
| [#10460](https://github.com/LionSR/TNLean/issues/10460) Fix \uses placement and word-only proof sketch in ch13_parent_hamiltonian_varying_obc.tex | [#6085](https://github.com/LionSR/TNLean/issues/6085) | needs-work | Fix uses placement and formula-driven proof text against the already-proved varying-OBC declarations. |
| [#10467](https://github.com/LionSR/TNLean/issues/10467) Add def:normal to the \uses list of thm:cpsv_physical_reindexing | [#8017](https://github.com/LionSR/TNLean/issues/8017) | needs-work | Add the actual normality definition to the physical-reindexing dependency list. |
| [#10468](https://github.com/LionSR/TNLean/issues/10468) Fix citation inaccuracies left unresolved after merge of #10289 | [#8274](https://github.com/LionSR/TNLean/issues/8274) | needs-work | Correct the cited source ranges and claims for the integrated Wielandt results. |
| [#10469](https://github.com/LionSR/TNLean/issues/10469) Fix stale citation range and missing \uses edges left unresolved after merge of #10309 | [#7685](https://github.com/LionSR/TNLean/issues/7685) | needs-work | Correct the uncle source citation and exact uses edges left after merge. |
| [#10470](https://github.com/LionSR/TNLean/issues/10470) Hoist ofFn_snoc_eq out of VaryingOBCReconstruction.lean to a shared Fin/List utility | [#4529](https://github.com/LionSR/TNLean/issues/4529) | needs-work | Move the generic finite-list snoc identity to a shared utility and migrate genuine callers. |
| [#10473](https://github.com/LionSR/TNLean/issues/10473) Derive wIndicator_flatten_cons from wIndicator_append instead of reproving the case split | [#4529](https://github.com/LionSR/TNLean/issues/4529) | needs-work | Reuse wIndicator_append in the flatten-cons proof instead of duplicating its case split. |
| [#10478](https://github.com/LionSR/TNLean/issues/10478) Sync blueprint \uses edges after the prime-length normal-block extraction in #10369 | [#10280](https://github.com/LionSR/TNLean/issues/10280) | needs-work | Update blueprint dependencies to the extracted generic prime-length normal-block results. |
| [#10479](https://github.com/LionSR/TNLean/issues/10479) Expose the nonnegative quadratic-form radical lemmas as reusable Algebra results | [#7685](https://github.com/LionSR/TNLean/issues/7685) | needs-work | Expose the reusable nonnegative quadratic-form radical facts in their proper Algebra owner. |
| [#10480](https://github.com/LionSR/TNLean/issues/10480) Add missing \uses{lem:prime_small_representation_fixed_tensor} to lem:spwc_bond_one_prime_ground_family | [#8274](https://github.com/LionSR/TNLean/issues/8274) | needs-work | Add the fixed-tensor prime-representation lemma to the bond-one family dependency list. |
| [#10481](https://github.com/LionSR/TNLean/issues/10481) Stale "Main statements" docstring in SupersiteHierarchy.lean after cfc_mem_supportedOperators move | [#9809](https://github.com/LionSR/TNLean/issues/9809) | needs-work | Update the supersite module summary after the functional-calculus ownership move. |
| [#10482](https://github.com/LionSR/TNLean/issues/10482) Promote generic rectangular-Kraus composition/trace lemmas from UncleTrialTransferNorm to QICLean | [#7685](https://github.com/LionSR/TNLean/issues/7685) | needs-work | Move the generic rectangular-Kraus composition/trace API upstream and migrate consumers. |
| [#10483](https://github.com/LionSR/TNLean/issues/10483) MPS/Periodic: the hypothesis `PeriodicEqualCaseFT` is false for d ≥ 1, D ≥ 2 | [#1809](https://github.com/LionSR/TNLean/issues/1809) | needs-work, scope-decision | Retire the false optional gauge route or use existing literal block data. Reuse the unaffected unconditional corollary; do not strengthen the broad family predicate silently. |
| [#10484](https://github.com/LionSR/TNLean/issues/10484) Reviewer-acknowledged blueprint fixes for the uncle energy-bound section did not land in merged #10321 | [#7685](https://github.com/LionSR/TNLean/issues/7685) | needs-work | Implement the acknowledged uncle energy-bound blueprint corrections that never landed. |
| [#10485](https://github.com/LionSR/TNLean/issues/10485) ch15_examples_pvbs.tex: flip resolved \notready tags and fix \uses/notation drift in the one-particle-window section | [#7685](https://github.com/LionSR/TNLean/issues/7685) | needs-work | Match one-particle-window readiness tags, dependencies and notation to the accepted proofs. |
| [#10486](https://github.com/LionSR/TNLean/issues/10486) Move RankOneWindowOverlap.lean out of the MPSPreparation namespace | [#7685](https://github.com/LionSR/TNLean/issues/7685) | needs-work | Move the rank-one window overlap API out of the preparation-specific namespace. |
| [#10487](https://github.com/LionSR/TNLean/issues/10487) Consolidate duplicated unital-power-contraction and density-projection lemmas in the uncle stack | [#7685](https://github.com/LionSR/TNLean/issues/7685) | needs-work | Consolidate repeated unital-power and density-projection facts and update the tactic ledger. |
| [#10488](https://github.com/LionSR/TNLean/issues/10488) Fix \uses misplacement around the uncle quantitative-factorization blueprint entries | [#7685](https://github.com/LionSR/TNLean/issues/7685) | needs-work | Put the uncle factorization uses edges on the statement/proof entries that actually use them. |
| [#10489](https://github.com/LionSR/TNLean/issues/10489) Justify or eliminate the silent [NeZero a] [NeZero b] hypotheses in uncleBoundaryLetter_mixedMapSpectralRadius_lt_one | [#7685](https://github.com/LionSR/TNLean/issues/7685) | needs-work, scope-decision | Check whether the existing hypotheses derive nonzero block dimensions; otherwise document a faithful restricted statement. The absent trace-one premise cannot be assumed. |
| [#10490](https://github.com/LionSR/TNLean/issues/10490) ch13_parent_hamiltonian_finite_prefix.tex: fix two blueprint/Lean equivalence mismatches in the Weyl word lemmas | [#8274](https://github.com/LionSR/TNLean/issues/8274) | needs-work | State the fifth-root hypothesis actually used and the all-degrees-at-least-eight charge result. |
| [#10491](https://github.com/LionSR/TNLean/issues/10491) Merge TNLean.Lattice.commutatorCLM with QICLean's GaussianFilter.commutatorCLM (opposite sign convention) | [#9828](https://github.com/LionSR/TNLean/issues/9828) | needs-work | Reconcile the opposite commutator sign conventions before upstream reuse; do not duplicate the expansion proof. |
| [#10492](https://github.com/LionSR/TNLean/issues/10492) Mark lem:hastings_gaussian_commutator_series ready now that its Lean proofs are complete | [#9828](https://github.com/LionSR/TNLean/issues/9828) | needs-work | Replace stale notready tags only for the two accepted Gaussian-expansion statement/proof anchors. |
| [#10493](https://github.com/LionSR/TNLean/issues/10493) Display the regional commutator and core-boundary identities in the original-chain robustness proof | [#9831](https://github.com/LionSR/TNLean/issues/9831) | needs-work | Display the regional commutator/annihilation and core-plus-boundary identities requested on merged #10371. |

## Exact-head open PR snapshot

Each base below is the actual remote branch tip at the cutoff. API cached
base OIDs and unknown mergeability alone were not conflict evidence.

| PR | Exact head | Actual base tip | Remaining-work labels |
|---|---|---|---|
| [#10248](https://github.com/LionSR/TNLean/pull/10248) feat(MPS/AreaLaw): construct physical DG improving families | [`99408b81b`](https://github.com/LionSR/TNLean/commit/99408b81b8882d787b3fd9ef9c63070d9487eb91) | `main` at `1c7d75bf8` | blocked, conflicts, needs-ci |
| [#10250](https://github.com/LionSR/TNLean/pull/10250) feat(MPS/AreaLaw): bootstrap physical ground spaces at every accuracy | [`fbafb1fa8`](https://github.com/LionSR/TNLean/commit/fbafb1fa862340b4532ab68f41cb6d81938a425a) | `codex/full-physical-dg-composition-20261027` at `99408b81b` | blocked, needs-ci |
| [#10254](https://github.com/LionSR/TNLean/pull/10254) feat(Lattice): product forms for varying local dimensions and Trotter active indices | [`ce497c351`](https://github.com/LionSR/TNLean/commit/ce497c351b8913b2d4ee592312ca22ddabe1989a) | `main` at `1c7d75bf8` | conflicts, needs-ci |
| [#10256](https://github.com/LionSR/TNLean/pull/10256) feat(MPS/AreaLaw): bound regional entropy in the full physical ground space | [`64f978f35`](https://github.com/LionSR/TNLean/commit/64f978f35aed47aa2f4d963168fd45f8398df639) | `codex/accuracy-physical-dg-bootstrap-20261027` at `fbafb1fa8` | blocked, needs-review |
| [#10326](https://github.com/LionSR/TNLean/pull/10326) feat(MPS/ParentHamiltonian): assemble generic finite-volume uncle gaplessness | [`bfd6637ba`](https://github.com/LionSR/TNLean/commit/bfd6637ba3aadbc2821f5bc5f9f65593e6c020a9) | `main` at `1c7d75bf8` | conflicts, needs-ci |
| [#10333](https://github.com/LionSR/TNLean/pull/10333) feat(MPS/Symmetry): derive connected clustering from the physical gap | [`38130b198`](https://github.com/LionSR/TNLean/commit/38130b19815fad299789ce715b80e5c27b00ada7) | `main` at `1c7d75bf8` | conflicts, needs-ci |
| [#10338](https://github.com/LionSR/TNLean/pull/10338) feat(MPS/Symmetry): derive virtual class invariance from the physical gap | [`df512ef0a`](https://github.com/LionSR/TNLean/commit/df512ef0a1508336ee156a8bdcf25b3597a3cdf0) | `feat/physical-positive-frequency` at `38130b198` | blocked, ci-failing |
| [#10341](https://github.com/LionSR/TNLean/pull/10341) feat(MPS/Symmetry): derive exact phase endpoint cohomology obstruction | [`4d823c4c5`](https://github.com/LionSR/TNLean/commit/4d823c4c549141168008ba0c1766e01cd4aba73f) | `feat/physical-window-clustering` at `df512ef0a` | blocked, needs-ci |
| [#10381](https://github.com/LionSR/TNLean/pull/10381) feat(MPS/CanonicalForm): construct physical quadratic windows and same-state converse | [`0ab64e2b1`](https://github.com/LionSR/TNLean/commit/0ab64e2b1fafebd7a3020735c3eabe1be4dfd640) | `main` at `1c7d75bf8` | conflicts, needs-ci |
| [#10388](https://github.com/LionSR/TNLean/pull/10388) feat(MPS/CanonicalForm): solve the prescribed canonical OBC window | [`7298d82cf`](https://github.com/LionSR/TNLean/commit/7298d82cf2eea6e1efa130d2f213edb42c41cc4a) | `main` at `1c7d75bf8` | blocked, conflicts, needs-ci |
| [#10403](https://github.com/LionSR/TNLean/pull/10403) feat(MPS/ParentHamiltonian): identify varying open projector kernels | [`b9de91ee9`](https://github.com/LionSR/TNLean/commit/b9de91ee9dfc411ab4ee7abbe9e18d3aee8bd3f2) | `main` at `1c7d75bf8` | conflicts, review-changes |
| [#10406](https://github.com/LionSR/TNLean/pull/10406) feat(MPS/ParentHamiltonian): derive the varying open parent ground-state line | [`56fcacee1`](https://github.com/LionSR/TNLean/commit/56fcacee1c2d5c8a18c2a31417e0872221ac3b26) | `main` at `1c7d75bf8` | blocked, conflicts, review-changes |
| [#10408](https://github.com/LionSR/TNLean/pull/10408) feat(MPS): derive the pure particle window Hamiltonian kernel | [`6c20b55ae`](https://github.com/LionSR/TNLean/commit/6c20b55aed007097070e0713d36afefded6c3ebc) | `main` at `1c7d75bf8` | needs-ci |
| [#10409](https://github.com/LionSR/TNLean/pull/10409) feat(MPS/Examples): identify the matching pure-particle ground line | [`55b5a3ab7`](https://github.com/LionSR/TNLean/commit/55b5a3ab7854a71b389b5de4f9676753674b78c3) | `main` at `1c7d75bf8` | blocked, conflicts, review-changes |
| [#10410](https://github.com/LionSR/TNLean/pull/10410) feat(MPS/ParentHamiltonian): transport parent terms across physical embeddings | [`104d70223`](https://github.com/LionSR/TNLean/commit/104d702236d64221058ac0d7a73ae00b72fbd6ff) | `main` at `1c7d75bf8` | blocked, conflicts, needs-ci |
| [#10411](https://github.com/LionSR/TNLean/pull/10411) feat(MPS): exclude mixed physical sectors from projector kernels | [`6e0e38927`](https://github.com/LionSR/TNLean/commit/6e0e38927bfc11b1d05946c482f16ec3096a391f) | `main` at `1c7d75bf8` | blocked, conflicts, review-changes |
| [#10412](https://github.com/LionSR/TNLean/pull/10412) feat(MPS): decompose actual ground vectors into physical sectors | [`2315edbb6`](https://github.com/LionSR/TNLean/commit/2315edbb6469612024fe78e1e57b56bba44dcc7e) | `main` at `1c7d75bf8` | blocked, conflicts, needs-review |
| [#10413](https://github.com/LionSR/TNLean/pull/10413) feat(MPS/ParentHamiltonian): transport the actual dependent physical parent sum | [`550bb47b7`](https://github.com/LionSR/TNLean/commit/550bb47b7363b8cffcb2a1a105a7813ef372fa61) | `main` at `1c7d75bf8` | blocked, conflicts, needs-review |
| [#10414](https://github.com/LionSR/TNLean/pull/10414) feat(MPS/Examples): reconstruct the short Weyl intersections | [`25b552eb8`](https://github.com/LionSR/TNLean/commit/25b552eb83eb097faa3c26e8d7abb909bb900831) | `main` at `1c7d75bf8` | needs-ci, review-changes |
| [#10415](https://github.com/LionSR/TNLean/pull/10415) feat(MPS/ParentHamiltonian): derive physical-sector component kernels | [`1cfbb6bf5`](https://github.com/LionSR/TNLean/commit/1cfbb6bf5ba37250209d13cbeb0412272fa06a90) | `main` at `1c7d75bf8` | blocked, conflicts, needs-ci |
| [#10416](https://github.com/LionSR/TNLean/pull/10416) feat(MPS/Examples): classify the periodic seven-site Weyl main kernels | [`efcb1cfb5`](https://github.com/LionSR/TNLean/commit/efcb1cfb5209b2bdfd381d31c892143092f398c2) | `main` at `1c7d75bf8` | blocked, conflicts, review-changes |
| [#10417](https://github.com/LionSR/TNLean/pull/10417) feat(MPS): identify the full physical-sector projector kernel | [`1eeab4b32`](https://github.com/LionSR/TNLean/commit/1eeab4b326c39369a7bc7e2103dc356b40e68c23) | `main` at `1c7d75bf8` | blocked, conflicts, needs-ci |
| [#10418](https://github.com/LionSR/TNLean/pull/10418) feat(MPS/Core): identify actual states under physical extension | [`a468491ad`](https://github.com/LionSR/TNLean/commit/a468491ad650c3e5e770f1c435e9d5c75c07c4b8) | `main` at `1c7d75bf8` | blocked, conflicts, needs-review |
| [#10420](https://github.com/LionSR/TNLean/pull/10420) feat(MPS/Examples): construct the fixed short-volume sector model | [`104f69dc8`](https://github.com/LionSR/TNLean/commit/104f69dc893f46e564a7d80eb8c605f9416e1ea8) | `main` at `1c7d75bf8` | blocked, conflicts, review-changes |
| [#10421](https://github.com/LionSR/TNLean/pull/10421) feat(MPS/ParentHamiltonian): derive physical support and compare actual parent kernels | [`b4e19782e`](https://github.com/LionSR/TNLean/commit/b4e19782e68fb47ceb58f7f435150cea8638fcf0) | `main` at `1c7d75bf8` | blocked, conflicts, needs-review |
| [#10422](https://github.com/LionSR/TNLean/pull/10422) feat(MPS/ParentHamiltonian): derive the varying-physical open ground line | [`1bbc456d5`](https://github.com/LionSR/TNLean/commit/1bbc456d558d519e6a9cee772b3dc1b121987d00) | `main` at `1c7d75bf8` | blocked, conflicts, needs-review |
| [#10426](https://github.com/LionSR/TNLean/pull/10426) feat(MPS/Examples): exhibit weighted canonical block cancellation | [`0b593fd95`](https://github.com/LionSR/TNLean/commit/0b593fd95d015c46e961591c00ccac0af5f5db77) | `main` at `1c7d75bf8` | conflicts, review-changes |
| [#10427](https://github.com/LionSR/TNLean/pull/10427) feat(Circuit/Channel): bound actual pure output approximation | [`bf6c7bcc6`](https://github.com/LionSR/TNLean/commit/bf6c7bcc6274ace13efbb76a0fc632b677b02885) | `feat/bounded-port-pure-output` at `a279041da` | blocked, ci-failing, conflicts |
| [#10432](https://github.com/LionSR/TNLean/pull/10432) feat(MPS/AreaLaw/ALVV): derive actual regional truncation residuals | [`48beacd53`](https://github.com/LionSR/TNLean/commit/48beacd531432b96b7c85aea171cde81417561ff) | `main` at `1c7d75bf8` | ci-failing |
| [#10433](https://github.com/LionSR/TNLean/pull/10433) feat(MPS/AreaLaw/ALVV): derive physical hard-truncation spectral comparisons | [`c51073e94`](https://github.com/LionSR/TNLean/commit/c51073e944a65f0f13476250e79c17341ac89184) | `feat/alvv-physical-middle-clipping` at `48beacd53` | blocked, conflicts, needs-ci |
| [#10434](https://github.com/LionSR/TNLean/pull/10434) feat(MPS/AreaLaw/AKLV): specialize parameters to frustration-free clipping | [`244c34c13`](https://github.com/LionSR/TNLean/commit/244c34c131d814b9defbba9bf1a2872f8519f347) | `feat/alvv-physical-hard-truncation` at `c51073e94` | blocked, needs-ci |
| [#10435](https://github.com/LionSR/TNLean/pull/10435) feat(MPS/AreaLaw/AKLV): filter the original frustration-free ground vector | [`7de0ab9b1`](https://github.com/LionSR/TNLean/commit/7de0ab9b1d1b7e73faaa0954a64c29fa79f70ce9) | `feat/aklv-frustration-free-parameters` at `244c34c13` | blocked, needs-ci |
| [#10436](https://github.com/LionSR/TNLean/pull/10436) feat(MPS/AreaLaw): bound original frustration-free entropy at every cut | [`fa4833e39`](https://github.com/LionSR/TNLean/commit/fa4833e39f774b9d0dbdcb3d35607842a4ed5e1e) | `feat/aklv-frustration-free-filter` at `7de0ab9b1` | blocked, conflicts, needs-ci |
| [#10455](https://github.com/LionSR/TNLean/pull/10455) feat(MPS/ParentHamiltonian): merge train block-degeneracy (17 PRs) | [`e44f46690`](https://github.com/LionSR/TNLean/commit/e44f46690c893983e49d12dc784b227a3c3bf605) | `main` at `1c7d75bf8` | needs-ci, review-changes |
| [#10464](https://github.com/LionSR/TNLean/pull/10464) feat(MPS/ParentHamiltonian): merge train parent-hamiltonian (22 PRs) | [`d39102c0b`](https://github.com/LionSR/TNLean/commit/d39102c0bc3f0c100e2c1ebeece57600df4a5fcf) | `main` at `1c7d75bf8` | needs-ci |

## Verification and historical snapshots

Read back changed labels, bodies, native-parent mutations and four COMPLETED
states. Compared selected accepted source against main, checked applicable
exact-head hosted CI/current reviews and actual-base read-only merge trees.
No local Lean, Lake, build, elaboration or checkdecls ran, and no PR was merged
by this refresh. The only local changes are Markdown audit records.

The [30 October triage](2026-10-30_non_qca_triage.md) preserves the previous
snapshot and its historical acceptance evidence. Its old pending-owner prose
is superseded by this dated queue, not rewritten as a new proof claim.
