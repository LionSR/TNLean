# Non-QCA issue delivery status, 29 October 2026

Snapshot base: main `c7d2992c89c16d85237e18557ff292979b3a67b4`.
The refreshed issue inventory has **192 open issues, including 55 trackers**.
These counts describe the queue, not mathematical completion. QCA remains
with Erickson and is omitted from this work.

This audit distinguishes source-written mathematics, exact-head hosted
acceptance, integration, external dependency release, and source-formulation
decisions. A closed child or successful unrelated check does not settle a
parent theorem. No repository merge is authorized by this audit.

## The two mathematical chains completed in source

| Issue | Actual result prepared | Delivery and remaining gates |
|---|---|---|
| [#10386](https://github.com/LionSR/TNLean/issues/10386), under [#10280](https://github.com/LionSR/TNLean/issues/10280) | One fixed positive range-seven interaction on five letters has a unique nonzero frustration-free ground line at every permitted M≥7, one actual bond-five tensor spanning every M≥8 ground line, and no nonzero ordinary TI trace-MPS ground vector at M=7, at any bond dimension. | [#10420](https://github.com/LionSR/TNLean/pull/10420), head `64199fb9a`. All local, mixed-sector, component and global kernel identities are derived. Two independent source/API reviews and native checks pass; hosted Lean acceptance and integration remain. |
| Theorem 9 in [#7684](https://github.com/LionSR/TNLean/issues/7684), under [#6085](https://github.com/LionSR/TNLean/issues/6085) | The actual adjacent open parent on arbitrary varying physical and bond dimensions has kernel equal to its actual normalized scalar-endpoint state line, with dimension one, for N≥2. | [#10422](https://github.com/LionSR/TNLean/pull/10422), head `77a8c4df9`. Physical support, common-alphabet construction, coefficient pullback, row/C1 preservation and parent comparison are derived internally. Independent source reviews and native checks pass; hosted acceptance/integration and the explicit short-chain convention remain. |

The #10386 construction obstructs the **all-permitted-volume ordinary
TI-trace upgrade**. It satisfies the eventual fixed-tensor conclusion and
does not refute general site-dependent MPS or an unspecified interaction
convention below seven sites. The exact source comparison is in
`docs/audits/2026-10-29_short_volume_sector_model.md` in #10420.

Theorem 11 in #7684 is a separate remaining boundary: [#10361](https://github.com/LionSR/TNLean/pull/10361)
proves the arbitrary positive-interaction block argument under explicit
gauge-phase separation. That condition still needs reconciliation with the
source's literal finite-ring-vector inequality. Theorem 9's completed
heterogeneous construction does not discharge it.

## Prepared implementation and integration queue

| Area and issue | Prepared draft chain | Precise next gate |
|---|---|---|
| OBC canonical form and representation freedom, [#6086](https://github.com/LionSR/TNLean/issues/6086) | [#10370](https://github.com/LionSR/TNLean/pull/10370) constructs actual canonical OBC data and rectangular representation freedom. | Reconciled with the snapshot main at `2b3c3006c`. Proof bytes are unchanged; fresh exact-head hosted acceptance and integration remain. |
| Prescribed-window quadratic TI reconstruction, [#6089](https://github.com/LionSR/TNLean/issues/6089) | [#10381](https://github.com/LionSR/TNLean/pull/10381) → [#10388](https://github.com/LionSR/TNLean/pull/10388). The latter constructs the actual quadratic solution on the original prescribed canonical window, deriving the bond bound, nonzero state, Perron normalization and cut gauges. | Reconciled heads `02c27b8ec` and `3beaa71ec` preserve the proof bytes and actual parent stack. Fresh hosted acceptance and integration remain. Preserve the source's full size regime and actual unchanged OBC coefficient state. |
| Half-chain fixed point and spectrum, [#6088](https://github.com/LionSR/TNLean/issues/6088) | [#10342](https://github.com/LionSR/TNLean/pull/10342) → [#10345](https://github.com/LionSR/TNLean/pull/10345). Concrete earlier diagnostics were repaired in `dfe9984f8`. | Current-main reconciliation preserves the repaired proof bytes; new hosted heads need their own acceptance. |
| Uncle limiting tensor, [#10284](https://github.com/LionSR/TNLean/issues/10284) | [#10317](https://github.com/LionSR/TNLean/pull/10317). | Reconciled head `941178794` preserves the actual perturbation/injectivity construction. Fresh hosted acceptance and integration remain. |
| Uncle periodic ground space, [#10285](https://github.com/LionSR/TNLean/issues/10285) | [#10320](https://github.com/LionSR/TNLean/pull/10320). | Reconciled head `621fcf9ba` preserves the full periodic kernel and repaired Haar-class arguments. Fresh hosted acceptance and integration remain. |
| Uncle finite-volume gaplessness, [#10286](https://github.com/LionSR/TNLean/issues/10286) | [#10324](https://github.com/LionSR/TNLean/pull/10324) → [#10325](https://github.com/LionSR/TNLean/pull/10325) → [#10326](https://github.com/LionSR/TNLean/pull/10326). | Reconciled heads `09629b8bf` / `400c79b06` / `beee2464f` include the existing-Haar-instance repair and concrete exact-head Gram-limit diagnostics fixed in `51d4f483e` (composition, rank-one trace and scalar-field inference). Fresh hosted acceptance remains. A small energy expectation alone is not the delivered result; the final statement concerns actual positive excitation eigenvalues relative to the full ground space. |
| Original-chain AKLV normalization, [#9837](https://github.com/LionSR/TNLean/issues/9837) | [#10371](https://github.com/LionSR/TNLean/pull/10371), above the integrated normalized robustness theorem. | Exact-head diagnostics were repaired in `5974e0c79`: the reserved identifier, associated matrix-product rewrites and interval-TeX lint. Reconciled head `0d91a2bd3` preserves the original unit bonds and derived regional common ground vector; fresh hosted acceptance and integration remain. |
| Hastings infinite Gaussian series adoption, [#10397](https://github.com/LionSR/TNLean/issues/10397), under [#9828](https://github.com/LionSR/TNLean/issues/9828) | [#10399](https://github.com/LionSR/TNLean/pull/10399) specializes the actual filter to the corrected operator-norm series at a concrete candidate dependency revision. | QICLean [#985](https://github.com/LionSR/QICLean/pull/985) acceptance and correction-note publication, accepted pin, TNLean hosted acceptance and integration. The finite-polynomial and actual Gaussian-integral bounds already integrated on main remain complete. |
| Redundant real-clearance corollary, [#10152](https://github.com/LionSR/TNLean/issues/10152) | [#10295](https://github.com/LionSR/TNLean/pull/10295) removes an unused specialization already implied by the stronger uniform linear bound. | Reconciled head `9832cebd0` preserves both retained source results byte-for-byte. Historical exact head `25b8b26cb` passed hosted full/strict and Blueprint web/PDF checks. Fresh combined-head acceptance and integration remain. |

The pure proof-reuse drafts [#10290](https://github.com/LionSR/TNLean/pull/10290)
(`f0a804558`, issue [#10258](https://github.com/LionSR/TNLean/issues/10258)) and
[#10304](https://github.com/LionSR/TNLean/pull/10304) (`45360f7ec`) now include
current main. Their historical exact heads passed hosted full/strict checks
for seven and two changed modules respectively; proof bytes are unchanged.
The generic cancellation owner [#10355](https://github.com/LionSR/TNLean/pull/10355)
is reconciled at `924f06d6a` with unchanged verified source. Fresh combined-head
acceptance and integration remain for each; the broader hypothesis audit is
not closed by one corrected anchor.

The SPT stack [#10333](https://github.com/LionSR/TNLean/pull/10333) →
[#10338](https://github.com/LionSR/TNLean/pull/10338) →
[#10341](https://github.com/LionSR/TNLean/pull/10341) is reconciled at
`52fb7d0c3` / `cec3907a1` / `f26255d0c`. Two missing Blueprint dependencies
now name the actual existing Lieb–Robinson entry. Proof bytes are preserved;
the endpoint module's scope documentation now states its exact-covariance
domain against the correct note. Current-head hosted acceptance is pending,
and [#2147](https://github.com/LionSR/TNLean/issues/2147) records that precise
classification boundary rather than claiming realizability is absent.

The nonabelian local physical renormalization PR
[#10364](https://github.com/LionSR/TNLean/pull/10364) is reconciled at
`0b9f106a0`, with its two verified Lean files unchanged. Its exact hosted
combined-diagram failure is repaired by including the actual new lemma in the
fragment. Two XeLaTeX passes give all 11 expected boundary signatures with no
unresolved reference, overflow or audit finding. The new local block proof
addresses [#8947](https://github.com/LionSR/TNLean/issues/8947) at that explicit
scope; full-lattice commutation, topology and parent transport remain open.

New source in these chains remains `notready` until its appropriate proof
acceptance. Native checks do not substitute for Lean. The current user
instruction is to write without local Lean/Lake/build/elaboration/checkdecls.

## Exact-head hosted evidence: five Wielandt leaves

The issue bodies were refreshed from the individual strict production-module
checks in the actual job logs, including the exact `PR_HEAD_SHA`, successful
full build and final strict-check success. All five issues remain open.

| Issue | Draft and verified source head | Individual changed Lean checks | Remaining gate |
|---|---|---:|---|
| [#10275](https://github.com/LionSR/TNLean/issues/10275) | [#10289](https://github.com/LionSR/TNLean/pull/10289), `2a9ea772` | 3/3 | Reconciled head `ba68e62be`; fresh exact-head acceptance and integration remain. |
| [#10276](https://github.com/LionSR/TNLean/issues/10276) | [#10294](https://github.com/LionSR/TNLean/pull/10294), `6ec6e186` | 2/2 | Reconciled head `83e2e92c2` on actual #10289 base; fresh acceptance and stack integration remain. |
| [#10277](https://github.com/LionSR/TNLean/issues/10277) | [#10302](https://github.com/LionSR/TNLean/pull/10302), `f3e72c028` | 2/2 | QICLean [#987](https://github.com/LionSR/QICLean/pull/987) acceptance, coherent accepted repin across all three dependency files, fresh acceptance and integration. Reconciled head `73ebff776` preserves the existing draft pin. |
| [#10279](https://github.com/LionSR/TNLean/issues/10279) | [#10307](https://github.com/LionSR/TNLean/pull/10307), `3a087f5c7` | 7/7 | Reconciled head `3c4b0a6de` needs fresh acceptance and integration; preserve the resolved missing-diagonal correction and the printed CP family without adding trace preservation. |
| [#10278](https://github.com/LionSR/TNLean/issues/10278) | [#10297](https://github.com/LionSR/TNLean/pull/10297), historical exact head `bebf891d8` | 2/2 | Reconciled head `47d921d10` preserves the three-Pauli source. Fresh exact-head acceptance and integration remain. |

The stochastic upstream PR remains draft/open. Its newer verified head is
`c4cbc544f7`, while the verified downstream snapshot explicitly pins `7a1bc092`.
Upstream green checks do not themselves accept or repin that dependency.

## Separate active area-law work

The live open-PR inventory already contains the following work. These are
ownership and delivery pointers, not a second implementation assignment or a
claim of current-head kernel acceptance:

- [#10404](https://github.com/LionSR/TNLean/pull/10404): AKLV entropy and sharp MPS approximation.
- [#10390](https://github.com/LionSR/TNLean/pull/10390): AKLV polynomial rank estimate.
- [#10331](https://github.com/LionSR/TNLean/pull/10331): inverse-gap robustness cutoff.
- [#10339](https://github.com/LionSR/TNLean/pull/10339): sampled viable-set induction.
- [#10362](https://github.com/LionSR/TNLean/pull/10362): Gaussian viable-set construction.
- [#10328](https://github.com/LionSR/TNLean/pull/10328): corrected ALVV frustration-free replacement, with the interior-region rank correction retained.
- [#10248](https://github.com/LionSR/TNLean/pull/10248), [#10250](https://github.com/LionSR/TNLean/pull/10250), [#10256](https://github.com/LionSR/TNLean/pull/10256): physical degenerate-ground-space constructions and entropy.

The unrestricted conclusions of [#9846](https://github.com/LionSR/TNLean/issues/9846)
and the other ALVV leaves must be compared with their actual hypotheses and
quantifier order before closing them from these references. The source's
running-time statements also remain separate from existence theorems.

## Integration already audited

The corrected Hastings hierarchy/thermal work is integrated in main through
[#10283](https://github.com/LionSR/TNLean/pull/10283). Issues
[#9851](https://github.com/LionSR/TNLean/issues/9851),
[#9852](https://github.com/LionSR/TNLean/issues/9852),
[#9854](https://github.com/LionSR/TNLean/issues/9854), and
[#10158](https://github.com/LionSR/TNLean/issues/10158) were closed only after
source and exact hosted evidence were checked. Their corrected hypotheses,
finite metric-growth distinctions, physical rounding and thermal constants
are recorded in their bodies. Parent #9828 remains open for its real remaining
Gaussian-series adoption child #10397.

Main now includes [#10379](https://github.com/LionSR/TNLean/pull/10379),
which synchronizes the three AKLV truncation results with their registered
lemma roles. `scripts/blueprint_roles.py --check` passes on the snapshot base.
The earlier isolated repair [#10359](https://github.com/LionSR/TNLean/pull/10359)
is superseded for this purpose. Draft reconciliation preserves main's chosen
roles and removes its obsolete robustness exception; statements, proofs and
declaration status are unchanged. No unrelated QCA cleanup is performed.

## Immediate operating order

1. Preserve the actual completed source and finish the small concrete hosted diagnostics.
2. Reconcile each draft with its actual PR base and preserve main's chapter moves.
3. Obtain new exact-head affected-source and Blueprint acceptance after each integration.
4. Resolve external accepted-pin/release gates at their owners.
5. Review the explicit source-domain and representation distinctions, then integrate and close only the acceptance criteria actually met.
