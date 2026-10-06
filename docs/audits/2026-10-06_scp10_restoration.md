# SCP10 restoration checkpoint — incomplete and uncompiled

## Provenance

The isolated branch `codex/scp10-quantum-double-restore` starts exactly at
`fc0d3ce4985baa3ffa0b16f6316830b2d64eb39a` (diagram PR #8727).
The archive commit is `ca5273cd335633e0aea2e4930c897d732b8260de`.
All 20 manifest SHA-256 values were verified before copying. Commit
`e31a8e340` contains byte-identical copies of the 19 in-scope files at their
original paths: 15 production modules, two tests, one blueprint leaf and one
historical audit. The archive branch was not merged. The braid module
`TorusCorrelatedChargePairCreation` was excluded.

The manifest labels six in-scope files as historical original hash matches and
13 as reconstructions. Four of those six also have matching entries in the
separate historical digest table. `QuantumDoubleOriginalGroundSpace` and
`QuantumDoubleOriginalHamiltonian` have no entry in that table: their original
match status is a manifest claim, not independently corroborated by that table.
Their snapshot bytes do match the manifest. The provenance JSON beside this
audit retains both distinctions.

`CommutingMatrixProjectionProduct` is **new implementation**, not byte recovery.
The pinned Mathlib source at `c55e6e786f49471c72fbddbec5415808896aec1e`
was consulted for `IsStarProjection.mul`, `Commute.list_prod_right` and
`Matrix.mulVec_mulVec`. No equivalent complete matrix list fixed-space API was
found by the source search. The proof uses factor absorption and list induction;
it has no assumed product-kernel equality. Its regression covers empty and
repeated lists and guards the two public results' standard axiom reports.
Neither the new proof nor the restored proofs have been compiled here.

Historical blueprint acceptance badges have been removed. The historical audit
has an explicit notice that its completion, review and old-pin assertions are
not current acceptance. Existing paper-gap statuses have not been superseded.
The blueprint leaf is not yet registered in the chapter router; its dependencies
and missing companion coverage must be reconciled after the proofs compile.
Generated production import aggregators do include the restored modules, so
the incomplete closure cannot be hidden from the ordinary root build.

## Source comparison performed

Read `Papers/1001.3807/paper_v3.tex`, lines 2858–2937 (Section 7.2), including
`eq:ex:doubles-renorm-tensor`. The printed elementary tensor is an unnormalized
coherent sum. The B averages in the restored code carry the separate factor
`|G|⁻¹`, as documented in the existing local Hamiltonian normalization gap note.
The preparation consumer states exactly `T = |G|^(2wh) Q |1,…,1>`; no scalar
was absorbed into an individual projector. The nonabelian clockwise tuple is
`(pq⁻¹, qr⁻¹, rs⁻¹, sp⁻¹)`.

This is a preliminary source reading, not a completed source-faithfulness review.
No new figure inspection or independent mathematical review is claimed. The
restored comparison retains `w,h ≥ 3`; native physical regrouping retains merely
positive coarse periods. Those hypotheses have not been changed.

## Remaining implementation frontier

The TN-source preflight visits 100 modules and currently fails on four imports:

1. `QuantumDoubleGlobalCheckerboardBlocking`: construct the actual local and
   global T-to-K contraction, in the orientation consumed by
   `QuantumDoubleNativeGlobalBlocking`; no selected-label surrogate.
2. `QuantumDoubleBlockingTransport`: use the actual physical regrouping matrix
   U, define the fine operator as `Uᴴ * H * U`, and transport annihilation and
   kernels with the correct adjoints on the full physical spaces.
3. `ToricCodePauliOperators`: supply the multiplicative binary group, `bitOne`,
   involutive site flips, placed diagonal Z parity and permutation X operators,
   and their coefficient-action lemmas.
4. `QuantumDoubleLatticeSourceParent`: this is not a thin import wrapper. The
   regression contracts require flat-supported gauge-invariant coefficients,
   reconstruction from flat configurations, orbit sums as actual twisted states,
   full commuting-closure spanning, the literal K/native-parent comparison and
   the complete commuting-pair conjugacy-class dimension. Their missing
   transitive layers still need new implementation.

The fifth original missing import, `CommutingMatrixProjectionProduct`, now has
source, but remains uncompiled and unreviewed. Missing declarations must not be
reintroduced as kernel, reconstruction, classification or blocking hypotheses.

## Checks and CI handoff

Passed locally: all 20 archive hashes; all 19 byte copies at the first checkpoint;
four source-closure guard tests (including rejection of stale objects and unknown
import syntax); three workflow guard tests; all 29 existing cache-policy tests;
generated-import completeness;
oversized-module policy; root/docbuild dependency-manifest agreement; and
`git diff --check`. A lexical scan of all 19 current Lean files (17 recovered,
two new) found no prohibited proof-escape tokens. This scan is not a kernel check.

`python3 scripts/check_scp10_restoration.py` deliberately exits 1 on the four
missing sources above. It checks only TN-source closure, not external dependencies
or elaboration. Its archive check needs the immutable archive Git object.

The ordinary PR CI now checks the lower layers early, after cache provenance
pruning and an explicit prebuilt `Mathlib.olean` guard:

- `CommutingMatrixProjectionProduct`;
- `FinitePermutationAverage`;
- `QuantumDoubleLatticeGauge` and `QuantumDoubleLatticeHamiltonian`;

The new projection-product regression and standard-axiom reports run only after
the full build, preserving the existing cache guard's requirement that direct
Lean invocations follow that build. The early check uses Lake and package options.

The post-build direct checks use `autoImplicit=false`, `relaxedAutoImplicit=false`,
`maxSynthPendingDepth=3`, the Mathlib standard linter and `warningAsError=true`.
The source-closure guard refuses incomplete imports after early compilation. The normal full root
build and style target are retained. Both recovered regression files are added
to the existing post-build test loop. No cache provenance rule or dependency pin
was weakened. A successful lower-layer check alone cannot establish acceptance.

There is no local Lean executable or prebuilt cache in this environment.
No Mathlib cache endpoint was retried, no mirror was sought, and no dependency
was rebuilt. GitHub API access via `gh` returned `Forbidden`, including an
approved sandbox escalation. Git fetch and draft-branch push work, but no PR or
CI run could be created or inspected. Normal exact-head CI and its results are
therefore the immediate operational blocker. Restore GitHub API access, open a
draft PR for this branch, and inspect the lower-layer results before extending
the uncompiled chain. The full closure, strict regressions, axiom checks,
blueprint checks and source-faithfulness review remain required.

No merge or deployment was performed. The open-boundary task, #8726, other-dot
GLM23 work and MPU-gauging code were not modified.
