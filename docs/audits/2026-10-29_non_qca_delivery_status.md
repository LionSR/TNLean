# Non-QCA issue delivery status, 29 October 2026

Implementation snapshot base: main `c7d2992c89c16d85237e18557ff292979b3a67b4`.
The latest main is `7b1ef717cec8bb851b433585e7b28cf4f7639208`; its accepted
QICLean pin update and PEPS chapter-role regrouping are integrated into this audit.
The refreshed issue inventory has **191 open issues, including 55 trackers**
after closing the completed Chebyshev leaf #9834.
These counts describe the queue, not mathematical completion. QCA remains
with Erickson and is omitted from this work.

This audit distinguishes source-written mathematics, exact-head hosted
acceptance, integration, external dependency release, and source-formulation
decisions. A closed child or successful unrelated check does not settle a
parent theorem. No repository merge is authorized by this audit.

## The two mathematical chains completed in source

| Issue | Actual result prepared | Delivery and remaining gates |
|---|---|---|
| [#10386](https://github.com/LionSR/TNLean/issues/10386), under [#10280](https://github.com/LionSR/TNLean/issues/10280) | One fixed positive range-seven interaction on five letters has a unique nonzero frustration-free ground line at every permitted M≥7, one actual bond-five tensor spanning every M≥8 ground line, and no nonzero ordinary TI trace-MPS ground vector at M=7, at any bond dimension. | [#10420](https://github.com/LionSR/TNLean/pull/10420), head `5b26a187f`. All local, mixed-sector, component and global kernel identities are derived. Two independent source/API reviews and native checks pass. The completed hosted build exposed finite-word and shared extension diagnostics, and its PDF job exposed an unregistered citation. Targeted repairs are published at the listed head; all other Lean blobs are unchanged. Fresh hosted Lean acceptance and integration remain. |
| Theorem 9 in [#7684](https://github.com/LionSR/TNLean/issues/7684), under [#6085](https://github.com/LionSR/TNLean/issues/6085) | The actual adjacent open parent on arbitrary varying physical and bond dimensions has kernel equal to its actual normalized scalar-endpoint state line, with dimension one, for N≥2. | [#10422](https://github.com/LionSR/TNLean/pull/10422), head `8560dffcc`. Physical support, common-alphabet construction, coefficient pullback, row/C1 preservation and parent comparison are derived internally. Independent source reviews and native checks pass. The completed hosted build exposed a wrong matrix API namespace and shared extension inference; its PDF job exposed missing bibliography metadata. Targeted repairs are published at the listed head through the original owners; unrelated Lean blobs are unchanged. Full bibliography generation and the native checks pass. Fresh hosted acceptance/integration and the explicit short-chain convention remain. |

The #10386 construction obstructs the **all-permitted-volume ordinary
TI-trace upgrade**. It satisfies the eventual fixed-tensor conclusion and
does not refute general site-dependent MPS or an unspecified interaction
convention below seven sites. The exact source comparison is in
`docs/audits/2026-10-29_short_volume_sector_model.md` in #10420.

The inherited bibliography repair is also propagated through the finite-prefix
ancestors #10366, #10369, #10376, #10396, #10407, #10414 and #10416. Each
owned change is exactly the same three citation keys in one chapter fragment;
all Lean blobs are unchanged and full bibliography generation passes.
GitHub reports #10369 conflicting although its exact base is an ancestor of
its exact head and the read-only merge-tree is clean. That external status
inconsistency is recorded without changing proofs or manufacturing a conflict.

Theorem 11 in #7684 has a separate source-formulation boundary:
[#10361](https://github.com/LionSR/TNLean/pull/10361) proves the arbitrary
positive-interaction block argument under explicit gauge-phase separation.
[#10426](https://github.com/LionSR/TNLean/pull/10426), head `4b3065ee5`, writes
an actual normalized 13-site counterexample to the literal weighted-vector
alternative: three nonzero canonical bond-one blocks satisfy C1 and pairwise
vector inequality, but two cancel and an actual positive interaction kills
the sum without killing the first block. Interpreting different states
projectively excludes the example. Its source/API review and native checks
pass. The current head also resolves its bibliography citation, with unchanged
Lean source and successful full bibliography generation; hosted acceptance and an explicit source-interpretation disposition
remain. This does not claim an unqualified refutation of the physical
statement or close #7684.

## Prepared implementation and integration queue

| Area and issue | Prepared draft chain | Precise next gate |
|---|---|---|
| OBC canonical form and representation freedom, [#6086](https://github.com/LionSR/TNLean/issues/6086) | [#10370](https://github.com/LionSR/TNLean/pull/10370) constructs actual canonical OBC data and rectangular representation freedom. | Reconciled with the snapshot main at `2b3c3006c`. Proof bytes are unchanged; fresh exact-head hosted acceptance and integration remain. |
| Prescribed-window quadratic TI reconstruction, [#6089](https://github.com/LionSR/TNLean/issues/6089) | [#10381](https://github.com/LionSR/TNLean/pull/10381) → [#10388](https://github.com/LionSR/TNLean/pull/10388). The latter constructs the actual quadratic solution on the original prescribed canonical window, deriving the bond bound, nonzero state, Perron normalization and cut gauges. | Reconciled heads `02c27b8ec` and `3beaa71ec` preserve the proof bytes and actual parent stack. Fresh hosted acceptance and integration remain. Preserve the source's full size regime and actual unchanged OBC coefficient state. |
| Half-chain fixed point and spectrum, [#6088](https://github.com/LionSR/TNLean/issues/6088) | [#10342](https://github.com/LionSR/TNLean/pull/10342) → [#10345](https://github.com/LionSR/TNLean/pull/10345). Concrete earlier diagnostics were repaired in `dfe9984f8`. | Reconciled heads `73b24fad5` / `5798fe3a5` preserve the repaired proof bytes and main c7 roles. New hosted heads need their own acceptance. |
| Uncle limiting tensor, [#10284](https://github.com/LionSR/TNLean/issues/10284) | [#10317](https://github.com/LionSR/TNLean/pull/10317). | Reconciled head `941178794` preserves the actual perturbation/injectivity construction. Fresh hosted acceptance and integration remain. |
| Uncle periodic ground space, [#10285](https://github.com/LionSR/TNLean/issues/10285) | [#10320](https://github.com/LionSR/TNLean/pull/10320). | Reconciled head `621fcf9ba` preserves the full periodic kernel and repaired Haar-class arguments. Fresh hosted acceptance and integration remain. |
| Uncle finite-volume gaplessness, [#10286](https://github.com/LionSR/TNLean/issues/10286) | [#10324](https://github.com/LionSR/TNLean/pull/10324) → [#10325](https://github.com/LionSR/TNLean/pull/10325) → [#10326](https://github.com/LionSR/TNLean/pull/10326). | Reconciled heads `09629b8bf` / `400c79b06` / `beee2464f` include the existing-Haar-instance repair and concrete exact-head Gram-limit diagnostics fixed in `51d4f483e` (composition, rank-one trace and scalar-field inference). Fresh hosted acceptance remains. A small energy expectation alone is not the delivered result; the final statement concerns actual positive excitation eigenvalues relative to the full ground space. |
| Original-chain AKLV normalization, [#9837](https://github.com/LionSR/TNLean/issues/9837) | [#10371](https://github.com/LionSR/TNLean/pull/10371), above the integrated normalized robustness theorem. | Exact-head diagnostics were repaired in `5974e0c79`: the reserved identifier, associated matrix-product rewrites and interval-TeX lint. Reconciled head `0d91a2bd3` preserves the original unit bonds and derived regional common ground vector; fresh hosted acceptance and integration remain. |
| Original-port pure output, [#8640](https://github.com/LionSR/TNLean/issues/8640), under [#8622](https://github.com/LionSR/TNLean/issues/8622) | [#10334](https://github.com/LionSR/TNLean/pull/10334) → [#10424](https://github.com/LionSR/TNLean/pull/10424). The new result derives the actual unitary output and normalized environment from a bounded native pure-state conversion, with the full all-operator channel identity and depth `2 * clog_d(B) * T`. | Reconciled head `40e62cc29` is source-reviewed and passes native checks; its statement/proof remain `notready`. Parent `ddc7cf488` preserves previously verified proof bytes. Fresh acceptance/integration and the separate approximate/control/resource obligations remain. No final-environment reset is asserted. |
| Approximate original-port pure output, [#8640](https://github.com/LionSR/TNLean/issues/8640) | [#10427](https://github.com/LionSR/TNLean/pull/10427), head `bf6c7bcc6`, derives Euclidean joint-vector error at most `sqrt(2 * ε)` from the actual full trace-norm channel error, retaining the same unitary, ports and depth. The input and target are normalized. | Generic coefficient/trace estimate is in QICLean [#1009](https://github.com/LionSR/QICLean/pull/1009), candidate `55528b03c`. Independent reviews and native checks pass; both new anchors remain `notready`. QIC acceptance, accepted coherent repin, fresh hosted acceptance and integration remain. No reset or adaptive-control conclusion is added. |
| W-state blocking and prime-divisor bound, [#2947](https://github.com/LionSR/TNLean/issues/2947) | [#10429](https://github.com/LionSR/TNLean/pull/10429), current head `8a24be18a`, derives the actual local isometry, normalized blocking identity and same-bond physical compression, then bounds every prime divisor of a positive represented length by the existing fifth-degree constant. | Two independent reviews and native checks pass. New anchors/proofs remain `notready`; hosted acceptance and integration remain. This extends composite coverage such as twice a large prime; it does not claim the full arbitrary-length or logarithmic-index result. |
| Two dead implementation helpers, [#9881](https://github.com/LionSR/TNLean/issues/9881) | [#10428](https://github.com/LionSR/TNLean/pull/10428), head `469715bd5`, removes only two unreferenced implementation helpers: minus 14 Lean lines, with every surviving source byte unchanged. | The exact scan difference is those two names, 32 to 30 candidates. Native/reference checks pass; hosted acceptance and integration remain. This is not permission to delete all zero-reference mathematical results. |
| Proper-cycle graph specialization, [#7936](https://github.com/LionSR/TNLean/issues/7936) | [#10310](https://github.com/LionSR/TNLean/pull/10310), head `d1c0a4fa9`, preserves both previously verified proof files after main reconciliation. General-graph deformation is already merged. | Fresh exact-head acceptance and integration remain for the actual proper-arc comparison, n≥3 and 0<L<n, including zero physical/bond dimensions. Full-ring and small-cycle boundary prescriptions stay explicit. |
| Corrected general AGSP entropy, [#9836](https://github.com/LionSR/TNLean/issues/9836) | QICLean [#1010](https://github.com/LionSR/QICLean/pull/1010), head `3d6ce4a8a`, derives actual product-overlap tails and the explicit bound `12 * (1 + log(μ⁻¹)/log(δ⁻¹)) * log D`, with rank-one and zero-shrinking endpoints. | Three independent reviews and native checks pass; seven public anchors remain `notready`. Hosted acceptance, integration and accepted pin remain. The printed formula's counterexample is preserved; the result concerns an invariant line, without a favorable-rank tradeoff assumption. |
| Frustration-free original-vector clipping, [#9838](https://github.com/LionSR/TNLean/issues/9838) | [#10430](https://github.com/LionSR/TNLean/pull/10430), head `3b93fea3d`, derives exact preservation of the original zero-energy unit vector and gap `g/2` after the actual two-sided clipping at `t ≥ 1024/g`, starting from raw supported positive unit bonds. | Independent reviews and native checks pass; the new anchor remains `notready`. Hosted acceptance/integration remain. The original-vector filter, scalar tradeoff and all-cut entropy assembly are now written in #10434–#10436 with inverse-gap logarithms retained. The sharper printed rate remains separate. No clipped gap or regional-commutation premise is supplied. |
| Frustration-free scalar tradeoff, [#9838](https://github.com/LionSR/TNLean/issues/9838) | [#10434](https://github.com/LionSR/TNLean/pull/10434), head `7be9879d2`, reuses the existing universal scalar theorem at `g/8192`. The actual cutoff `1024/g`, half-gap and window yield `Dδ ≤ 10⁻⁵`, window cost `C u²/g` and logarithmic-rank cost `C u³/g`, with `u=1+log q+log(1/g)`. | Independent full source/API reviews and native checks pass; the new statement/proof remain `notready`. No absorption proof is copied and no actual excitation is assumed. Hosted acceptance and stack integration remain; inverse-gap logarithms are explicit. |
| Original-vector frustration-free filter, [#9838](https://github.com/LionSR/TNLean/issues/9838) | [#10435](https://github.com/LionSR/TNLean/pull/10435), head `ac41990d8`, derives one actual clipped Hamiltonian and Chebyshev polynomial fixing the original unit vector, with half-gap, actual norm ceiling, shrinking and the same-operator same-cut rank bound. | Root and two independent full reviews and native checks pass; both new anchors remain `notready`. Exact #10430 clipping source/entry is preserved as an explicit logical prerequisite. Original bonds determine all geometry, clipping, spectral ceiling and target; no first-excited-energy hypothesis is supplied. Hosted acceptance, accepted pin and integration remain. |
| All-cut original-vector frustration-free entropy, [#9838](https://github.com/LionSR/TNLean/issues/9838) | [#10436](https://github.com/LionSR/TNLean/pull/10436), head `03ec58ed0`, proves one universal bound `S ≤ C (1+log q+log(1/g))³/g` for the original unit vector at every physical cut and every chain length, for `q ≥ 2` and `0 < g ≤ 1`. A fitted window uses #10435; endpoint and short-chain cases use the existing smaller-side dimension bound. | Root and two independent full reviews and all native checks pass; the two new statement/proof entries remain `notready`. The only change to existing Lean is visibility of the exact existing short-side lemma, with its signature/proof bytes unchanged. No excitation, product-overlap, tail, filter or window-fit premise is supplied. Hosted acceptance, upstream accepted pin and stack integration remain; the sharper printed rate without inverse-gap logarithms remains open. |
| Restricted low-energy comparison, [#9844](https://github.com/LionSR/TNLean/issues/9844) | QICLean [#1011](https://github.com/LionSR/QICLean/pull/1011), head `c04b69cdc`, gives ordered eigenvalue comparison from the actual canonical restricted norm. Child [#1013](https://github.com/LionSR/QICLean/pull/1013), head `4e688e3d8`, derives the actual ground-energy displacement and both relative-ground-energy closeness statements, with the explicit ceiling-window remainder. | Independent mathematical and pinned-API reviews and native checks pass. Both new statement/proof entries remain `notready`; acceptance, accepted pin and the actual physical-chain application remain. No minimum, eigenbasis, ground shift or closeness conclusion is supplied. |
| Physical single-region truncation estimates, [#9844](https://github.com/LionSR/TNLean/issues/9844) | [#10432](https://github.com/LionSR/TNLean/pull/10432), head `c8ca41cdb`, derives three actual regional minima, common unit minimizer, both actual centered ground energies in `[0,2]`, and both canonical restricted-error estimates `32 exp(−(t−η)/8)` at `t ≥ η+7`. Coincident and endpoint cuts are included. | Three independent source/API reviews and native checks pass; the new statement/proof remain `notready`. Actual parent #10404 and its existing QIC candidate `716753c0` remain prerequisites. The comparison client is now written in #10433; its hosted acceptance, upstream prerequisites and coherent accepted pin remain distinct gates. The only inherited repair aligns four AKLV Blueprint role sites with main; parent Lean bytes are preserved. |
| Corrected physical hard-truncation comparison, [#9844](https://github.com/LionSR/TNLean/issues/9844) | [#10433](https://github.com/LionSR/TNLean/pull/10433), head `a2c707dd2`, combines #10432 with the actual canonical minimum identities, ordered eigenvalue bounds, ground displacement and both relative spectral-space comparisons. The explicit enlargement is `η+ξ+2ξ sqrt(ceil(η/(2ξ))/δ)`, with `ξ=32 exp(−(t−η)/8)` and `t ≥ η+7`. | Three independent source/API reviews and all native checks pass; the new statement/proof remain `notready`. All three dependency records coherently select assembly `fc38c6bd`, whose two added mathematical files are byte-identical to reviewed QIC #1011/#1013; all other existing `716753c0` Lean files, notes and dependency pins are preserved. Upstream acceptance, note #1012 publication, accepted repin, hosted proof acceptance and stack integration remain. This does not assert the false unrestricted `t>η` statement or a uniform small-η asymptotic formula. |
| Hard-truncation cutoff obstruction, [#9844](https://github.com/LionSR/TNLean/issues/9844) | [#10431](https://github.com/LionSR/TNLean/pull/10431), head `620e1af0d`, constructs actual nearest-neighbor positive unit bonds with regional minimum zero and both actual global minima `3/4`. At fixed `t=3/2>η=1`, the actual truncated low-energy projection has discrepancy at least `K−3/2`, unbounded with length. | Two independent reviews and native checks pass; the new example remains `notready`. QICLean [#1012](https://github.com/LionSR/QICLean/pull/1012), head `0cf09da9f`, updates the existing window note. The example obstructs the unrestricted truncated-side bound only; the original-side bound and a sufficiently large explicit cutoff remain separate. |
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

The trace-form migration [#10292](https://github.com/LionSR/TNLean/pull/10292)
keeps its verified head `73c47deec`: every applicable check, including web/PDF,
now passes. Read-only merge-tree against the snapshot main is clean, and main
has no edits to its seven owned Lean paths. No new source repair is warranted;
[#7850](https://github.com/LionSR/TNLean/issues/7850) stays open for final
combined-head acceptance, review and integration.

The nonabelian local physical renormalization PR
[#10364](https://github.com/LionSR/TNLean/pull/10364) is reconciled at
`0b9f106a0`, with its two verified Lean files unchanged. Its exact hosted
combined-diagram failure is repaired by including the actual new lemma in the
fragment. Two XeLaTeX passes give all 11 expected boundary signatures with no
unresolved reference, overflow or audit finding. The new local block proof
addresses [#8947](https://github.com/LionSR/TNLean/issues/8947) at that explicit
scope; full-lattice commutation, topology and parent transport remain open.
[#10425](https://github.com/LionSR/TNLean/pull/10425), head `ee4ad0b28`, audits
the claimed older completion packets: the located restoration is incomplete,
contains reconstructed rather than original files and lacks the source-parent
proof dependency. Historical review prose is not delivered proof evidence.

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

- [#10402](https://github.com/LionSR/TNLean/pull/10402): bounded-width strips, with the actual snake geometry, original-space entropy and MPS approximation. An independent source audit confirms the construction and exact-head three-module hosted strict success at `9733d9f44`; full acceptance/integration remain.
- [#10404](https://github.com/LionSR/TNLean/pull/10404): AKLV entropy and sharp MPS approximation.
- [#10390](https://github.com/LionSR/TNLean/pull/10390): actual same-Hamiltonian AKLV polynomial rank estimate. Its existing remote head `6f11ba0df` has an active hosted build. A local reconciliation with main preserves all 12 owned Lean files byte-for-byte and coherently retains the candidate QIC pin. The completed web failure identifies two interval-bracket lint diagnostics, already repaired locally. Publication of that reconciliation is held until the old build finishes so its proof diagnostics are preserved; active jobs are not acceptance evidence.
- [#10331](https://github.com/LionSR/TNLean/pull/10331): inverse-gap robustness cutoff.
- [#10339](https://github.com/LionSR/TNLean/pull/10339): sampled viable-set induction.
- [#10362](https://github.com/LionSR/TNLean/pull/10362): Gaussian viable-set construction.
- [#10328](https://github.com/LionSR/TNLean/pull/10328): corrected ALVV frustration-free replacement, with the interior-region rank correction retained.
- [#10248](https://github.com/LionSR/TNLean/pull/10248), [#10250](https://github.com/LionSR/TNLean/pull/10250), [#10256](https://github.com/LionSR/TNLean/pull/10256): physical degenerate-ground-space constructions and entropy.

The unrestricted conclusions of [#9846](https://github.com/LionSR/TNLean/issues/9846)
and the other ALVV leaves must be compared with their actual hypotheses and
quantifier order before closing them from these references. The source's
running-time statements also remain separate from existence theorems.

## Genuine mathematical boundaries

These are not missing short wrappers or requests for duplicate implementations.
Their issue bodies now separate existing results from the remaining claim.

| Issue | Already present | Actual remaining boundary |
|---|---|---|
| [#8885](https://github.com/LionSR/TNLean/issues/8885) | Merged #9096 constructs faithful stationary support compression from actual positive nonzero stationary data and preserves all expectations; continuous state equality and actual compressed local support are implemented. | Construct normalized stationary data from the original general GVBS boundary limit while preserving that limit, then construct a minimal faithful representation of the generated auxiliary observable algebra. Full stationary support alone does not imply that algebraic minimality. |
| [#8469](https://github.com/LionSR/TNLean/issues/8469) | Actual non-normal fixed-point data, compatible-seed conversion and coherent conversion of matched sector encoders are on main. | The chosen finite-ring sector coefficients need justified transport. Main's identical-parent GHZ example has infidelity at least `9/5000` for `N > 4T+4`; sharing a parent/phase alone does not identify arbitrary selected vectors. The source's length-dependent coefficients and measurement-prepared seed remain explicit. |
| [#2947](https://github.com/LionSR/TNLean/issues/2947) | Merged #8386 derives a canonical reduction and fifth-degree W-state bound in the no-small-divisor regime. Draft #10429 now derives the actual normalized local blocking isometry, same-bond compressed tensor and a bound on every prime divisor of a represented length. | Obtain acceptance/integration of #10429; control arbitrary composite lengths, including surviving periods and repeated small prime factors; formalize the separate Michałek–Shitov logarithmic exact-word-span bound in the channel library. The prime-divisor bound, eventual Hamiltonian dichotomy and finite-prefix model do not imply a bound on all lengths. |
| [#8947](https://github.com/LionSR/TNLean/issues/8947) | Merged local K constraints/averages and the new one-block nonabelian renormalization result. | Actual full-lattice placement and all commutators, topological common-kernel classification, and comparison with the PEPS parent. The recovered incomplete archive is not their proof. |

The exact frustration-free clipping theorem #10430 settles preservation and
its inverse-gap cutoff. It does not finish the sharper AKLV parameter step:
the original source's lines 840–843 drop the displayed `log(s²+s)` term.
At fixed local dimension and `s` proportional to `1/g`, the current rank
certificate has logarithm of order `log(1/g)/g`, while the shrinking
certificate has negative logarithm of order `1/g`. These certificates do not
establish the printed uniform sharper rate. This does not bound the actual
operator Schmidt rank from below or refute the sharper area law. Issue #9838
records the exact remaining rank/parameter mechanism and stays open.

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

The Chebyshev scalar/operator leaf [#9834](https://github.com/LionSR/TNLean/issues/9834)
is closed as completed. Its exact requested degree, normalization, upper-interval
contraction, left-side order and isolated-energy operator consequences are
already accepted in QICLean. Current TNLean pin `14ecc5b6` preserves the three
source files byte-for-byte from `acda92aa`; exact accepted runs at both pins
pass full/strict Lean and Blueprint compilation. The closure explicitly
excludes the additional near-threshold ALVV clause, positivity of the unsquared
filter, rank bounds and chain assembly. Those separate obligations are not
silently included.

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
