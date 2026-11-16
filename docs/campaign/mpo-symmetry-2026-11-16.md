# MPO symmetry campaign — 2026-11-16

## Claimed scope and baseline

Owner: the separate campaign delegated from thread `6af54194-8060-8191-9800-f45dd86d90e6`.
Branch: `feat/10521-controlled-z-combined-symmetry`. Issue: #10521, combined family and
relative action class; the physical phase theorem remains open.
Claim comment: https://github.com/LionSR/TNLean/issues/10521#issuecomment-6903716068.

Provisioned TNLean was clean at `eb588dc15332a3798431015e6c27ecbaf329b2d1`.
Fetched upstream main is `73007e10337424b3556fb198507b2157f99f19a3`; this branch starts there.
The provisioned dependency directories were stale too: QICLean `acda92aa` and Mathlib
`c55e6e78`. The manifest requires QICLean `603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac`,
Mathlib `625d8914199bc567cca9b91f90e8e5afafa5ae51`, and Lean `v4.36.0-rc1`.
Restore those exact pins and fetch prebuilt Mathlib artifacts before any build.
Do not use the provisioned v4.35 artifacts or rebuild Mathlib from source.

## Refreshed ownership and dependency map

The live issue bodies, comments, open-PR inventory (59 PRs), and every open-PR file list
were read before implementation. Thread interiors are unavailable in this environment;
thread ownership below combines the delegation with current GitHub evidence.

| Scope | Current evidence | Campaign boundary |
| --- | --- | --- |
| #8321 | #10626 draft, `b554532d`, stacked on `761f6a56`; #10615 `d6b3712c`, #10616 `3ba155b6` remain drafts | Preserve existing owner and prerequisite order. ControlledZGauging and cochain sources are occupied; add separate consumers only. |
| #8322 | #10636 draft `2475f50b`; universal/bridge local branches reported in delegation | No based-ring implementation or consumer migration here. Preserve local unverified bridges. |
| #8053 item 2 | Existing Fibonacci owner; issue says actual two-block L=F remains | No takeover or duplicate symbolic calculation. |
| #8048/#8054/#8948 | tnlean-35; #8948 comments claim `feat/mixed-path-mpo-batch` | Preserve time reversal, arbitrary-boundary adapter, Hamiltonian commutation and degenerate interpolation. |
| #8040 | tnlean-43 | No CZX PEPS changes. |
| #10519 | Abstract pre-bialgebra family construction remains; #10517/#10526 merged | Faithful unital representation alone does not imply cosemisimplicity. Supplied-family counit does not solve this. |
| #10521 | Open, unassigned, zero comments before campaign claim; no open SIMPS PR found | Claim exact combined normal MPO family, actual split-leg/ring comparison, and two invariant states. Full phase identification remains open. |
| #8050 | Updated status confirms algebraic foundations on main; physical invariance/interpolation remain | No claim of the full L-class/physical-phase biconditional. |
| #6024/#6140 → #7032 → #7016 | Active continuous-standard-form owner from delegation | No MPU path-source-data changes. |
| #9880 | Active intrinsic-deformation owner from delegation | No sign-deformation changes. |
| #8060 | #10641 draft `dac8ae0a` | Preserve conditional detector/physical-anomaly distinction. |
| #7574 | #10640 ready `3c4ede7d`, updated since handoff | Existing owner; final-head CI/review still required. |
| Refactoring stack | #10676 `7c16e494` → #10677 `c5ddd838` → #10678 `064e2daa`, all drafts | No occupied source edits or cherry-picking. Independent new modules only. |

No labels, assignees, PR bases, workflow approvals, or issue states were changed by this audit.
#10616's reported workflow approval gate must be handled by its authorized owner/maintainer.
Live workflow read confirms PR CI run `43744473685` remains `action_required`.
Skipped auto-fix workflows do not clear that gate.

## Mathematical dependency order

1. Reuse existing diagonal dressing and letter-rescaling normality; prove a commuting
   diagonal twist of an exact normal group family is again exact and normal.
2. Instantiate the construction for the combined controlled-Z/on-site Z symmetry on the
   actual qubit chain, using the existing controlled-Z family and character on the other bit.
3. Identify its operator with the product of the existing split-leg phases on the ring;
   derive invariance of the controlled-Z state and reference product state at every positive
   length, including length one. Obtain actual action/fusion data through existing results.
4. Compute and compare the two actual L-symbol classes (completed in the continuation).
   Remaining: physical path invariance or a source-faithful physical classification.

## First-head results and validation

Both new proof modules pass the package build and direct strict Lean elaboration, including
`autoImplicit=false`, `relaxedAutoImplicit=false`, the package's synthesis-depth bound,
standard Mathlib linters, and warnings as errors. All 22 new public declarations have
transitive foundational dependency sets contained in `{propext, Classical.choice, Quot.sound}`.
The temporary audit command file was deleted. No full-library or compiled Blueprint acceptance is
claimed.
The new shared construction belongs in `MPOSymmetry/DiagonalTwist.lean`; the controlled-Z
consumer belongs in a separate example module, avoiding the #8321 source overlap.

Verified mathematical results:

- A commuting diagonal on-site twist preserves the exact normal group multiplication
  law and the original bond dimensions. Every common invariant state remains invariant.
- The combined controlled-Z/on-site Z family has bond dimension one or two, is normal,
  and has the literal identity operator. Its operators form a native Mathlib representation.
- Its actual operator equals the diagonal product of the existing split-leg phases on
  every positive ring length, including one. Those operators are unitary.
- The existing bond-three controlled-Z state and bond-one zero product state are both
  fixed. Actual action reductions exist for each under the same family. The anomaly
  class is zero. This last statement is in degree three, not the missing relative
  degree-two class comparison.

Exact local verification commands and evidence (2026-11-16):

```
lake build TNLean.MPS.Symmetry.MPOSymmetry.DiagonalTwist \
  TNLean.MPS.Examples.ControlledZCombinedSymmetry
```

Passed, 18,895 jobs in the focused dependency closure. This is **not** the full library
build. Dependency modules emit their existing legacy-module/style warnings; both new
sources pass independently with all warnings treated as errors:

```
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dpp.unicode.fun=true -DmaxSynthPendingDepth=3 \
  -Dlinter.mathlibStandardSet=true -DwarningAsError=true <new-proof-source>
```

Also passed: generated-import check (98 aggregators, 5,420 production modules),
Blueprint source synchronization with reverse coverage of both new modules, Blueprint
roles, the complete repository text-style linter, reader-facing prose, forbidden-token
scan, 100-character line bounds, and
`git diff --check`. The focused tactic-pattern scan found no promoted/new repeated
pattern in these modules; unrelated pre-existing candidates remain with their owners.
All 22 public names occur in the new Blueprint entries. Source synchronization is
distinct from compiled full-library declaration checking and web/PDF generation.

The initial cache command stopped because its default `/home/agent/.cache` is read-only;
retry uses `XDG_CACHE_HOME=/workspace/.cache`. Only the cache executable was compiled.
The exact prebuilt artifact fetch completed (9047 artifacts); no Mathlib Lean source module
was rebuilt. The style executable compiled its required C objects from the cached artifacts.
Dependency pins and tracked configuration are unchanged. The new modules use the
same legacy import convention as their existing dependencies: this Lean version rejects
importing those non-`module` dependencies from a `module` file.

## Candidates and blockers

- The initial relative L-symbol candidate is completed by the continuation below.
- The full SIMPS physical phase theorem is absent, and the paper-gap note stays open.
- Final-head focused strict elaboration, full library/Blueprint CI, required proof and
  Blueprint review, and dependency-order integration are required before any normal merge.
- Preserve the shared tactic ledger owned by #10677. Record any abstraction decision here.
  The diagonal construction reuses existing mathematical lemmas rather than adding a tactic.

## Continuation: actual relative L-symbol class

PR: https://github.com/LionSR/TNLean/pull/10686. The first proof head is
`0d04e49205be890d7e735f2899b7500c29ae56ee`; subsequent final heads are recorded in the PR.
Its independent source/Blueprint review found no blockers at that first head
(https://github.com/LionSR/TNLean/pull/10686#issuecomment-6903972219 is the request;
the review is the later claude[bot] reply). That review is historical evidence for the
first head, not approval of the extended result. The current PR CI run is
https://github.com/LionSR/TNLean/actions/runs/43780545166; its build job started after
the runner queue. No completed full-CI pass or required formal approval is inferred.

The continuation proves the missing relative calculation, including independence of all
reduction choices:

1. `ReductionCertificates` maps Kronecker and local compression identities from a coefficient
   ring into complex matrices. Existing all-word reduction theory supplies the conclusion.
2. `ControlledZCombinedReductions` supplies explicit rational action caps for the bond-three
   state and reference product state, plus common fusion caps. Kernel reduction checks the
   finite cap, letter, and projection-insertion identities; the actual reductions hold on
   every word. The action caps for controlled-Z require transient directions; a bare
   one-letter square gauge is not assumed.
3. `LSymbolComputation` uses the sufficient one-letter relation between the two action
   trees. Multiplication by the rest of the word gives dressed proportionality directly;
   no redundant two-letter intertwiner assumptions are needed. Normality and the actual
   reduction give nonvanishing and uniqueness of the selected L-symbol.
4. The actual scalar values are `L_A((p,q),(r,s)) = (-1)^(p*s) * 4^(q*s)` and `L_0 = 1`.
   Their ratio is a native Mathlib two-cocycle and differs from the existing cluster
   cocycle `(-1)^(q*r)` by the coboundary of `phi(p,q) = (-1)^(p*q) * 2^q`.
5. `SingleBlockLSymbolGauge` specializes the existing permuted-block gauge law to one block.
   In the relative factor the common fusion gauge cancels; changing either state's action
   caps contributes only a coboundary. No duplicate cochain type is introduced.
6. `combinedRelativeLSymbol_H2π_eq_cluster` and `combinedRelativeLSymbol_H2π_ne_zero` apply
   to **every** actual action and common fusion choice for the two fixed states. This is
   stronger than merely calculating a chosen table or its commutator.

The complete seven-module proof batch passes the combined package build (19,077 jobs
in its focused closure) and strict direct checks with all package options and warnings as
errors. All 69 public declarations have foundational dependencies contained in the three
standard logical principles. The two computational modules built in 21 and 19 seconds,
below the compilation-time failure threshold. Full source synchronization, reverse
coverage, Blueprint roles, repository-wide text style, generated imports, prose and
integrity checks are recorded separately from hosted full-library/compiled-Blueprint
acceptance. The temporary foundational audit command file was removed.

Upstream main advanced to `2e0e6387c156ff7449a4f1df51775a5a5d2144cf` during the work.
The intervening changes are lattice/area-law work and two additional promoted-pattern
entries in `CLAUDE.md`, which were read. No intervening changed source is in the new
capstone's 268-module transitive TNLean import closure. This actual main is integrated
before publishing the extended head, preserving the exact checked proof sources and pins.

The refreshed inventory contains 75 open PRs. The 17 newly observed PR file lists have
no overlap with the selected new proof or Blueprint files; one is this campaign's own
PR. Fibonacci now has its owner's draft #10689, so that scope remains occupied.

### Physical source audit and remaining dependency

Primary source: https://arxiv.org/html/2404.15883v2, Sections 3.4, 3.4.4 and 6.3.
Stephen proves a symmetric finite-depth circuit obstruction and a fingerprint theorem
for a circuit-defined phase. The general SIMPS interpretation of the L-symbol
classification is posed as a question in Section 6.3. Thus the issue's gapped-path
target still needs a physical path theorem or a proved connection to that circuit notion.
The existing gap note is corrected to preserve this distinction, without changing the
requested gapped-path target.

Remaining: derive invariance of the actual relative class along the source's allowed
physical paths, or formalize the source circuit obstruction and the required connection
to that path notion. The family, explicit reductions and reduction-independent relative
class are no longer missing. A supplied virtual/projective path is not a replacement for
the physical path construction.

### Coordination and abstraction decisions

- Notified #10626's owner on its PR before constructing the new reductions; no occupied
  source was edited. The new single-block gauge adapter reuses `PermutedBlocksGauge`.
  These new consumers must be included in the eventual cochain-migration integration audit.
- The new one-letter dressed-proportionality lemma could simplify the existing toolkit's
  stronger local lemma. Leave that occupied source to #10626's owner, rather than making
  a competing refactor. No custom tactic is added, and the shared tactic ledger stays intact.
- All rational calculations are candidates until their Lean certificates are checked;
  the published results use the checked certificates and actual tensor equalities.
- Addressed both non-blocking observations in the first-head independent review: the
  Blueprint explicitly distinguishes the two-leg phase from the one-leg character, and
  the Blueprint/gap note state the repeated-bit convention at ring length one. Fresh
  review is still required for the extended head.
