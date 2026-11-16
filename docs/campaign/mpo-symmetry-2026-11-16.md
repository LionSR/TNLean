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

### Final integration and physical dependency checkpoint

- Integrated upstream main `2e0e6387c156ff7449a4f1df51775a5a5d2144cf`. None of
  the intervening changed Lean sources belongs to the new modules' 268-module TNLean
  transitive import closure. The exact integrated seven-module build passes (19,077 jobs).
- Refreshed #8050's source requirements directly from
  `Papers/2203.12563/REsubmission.tex`, definitions `defsym` and `defphase`: importing the
  physical classification requires arbitrary-boundary fusion closedness and an injective
  symmetry embedding along the path. Periodic group multiplication and action/fusion
  reductions alone do not verify those premises for the combined controlled-Z family.
- #7332 is closed for the algebraic stabilizer/cohomology classification, according to
  its current issue body; its title must not be read as a completed physical path theorem.
- The parent explicitly reconfirmed that #8053 remains occupied, with recovery of the
  disconnected owner's local artifacts pending. No implementation takeover is attempted.
- The pinned LaTeX formatter detected whitespace in the two changed Blueprint chapters;
  both are now formatted and pass its check. Paper-gap references resolve (308 slugs).
  This documentation repair changes no Lean source, hypotheses, or proof terms.
- The independent Codex review of the first extended head completed with no findings.
  Fresh proof/Blueprint review and exact-final-head hosted CI remain merge requirements;
  a replacement documentation head must be checked and reviewed too.

## Continuation: actual reduction paths and the closed-fusion obstruction

The next mathematical batch was developed on
`feat/10521-mpo-action-path-invariance`, based on the frozen relative-class head
`65a98e1361f0f03216df6e77112116c17965aba6`, while that head was reviewed. Its
four new modules form one coherent continuation of #10686, rather than separate small
PRs. The parent reconfirmed preservation of Fibonacci scope; no takeover occurred.

### Checked mathematical results

- `LSymbolContinuity` derives the common comparison threshold `|w| > 2E` from the
  source bond dimension `E`. Continuous source tensors and left reduction caps then
  give continuous selected dressed scalars, by a nonzero-entry quotient near each point.
  Neither target tensors nor right caps need be continuous for this generic lemma.
- The same module proves continuity of actual MPO action tensors, both actual action
  trees, and their selected single-block L-symbols from continuous state tensors and
  left action caps. It uses actual all-word reductions, normality, positive fixed state
  bond dimension and periodic invariance; no continuous scalar is assumed.
- `FiniteCocyclePath` proves endpoint cohomology invariance for any continuous scalar
  two-cocycle path on a finite group. The regular matrices are constructed from the
  cocycle and the existing determinant-root path argument is reused. A virtual
  projective matrix path is not supplied as a premise.
- `LSymbolPathInvariance` cancels the common associator between two actual invariant
  states and derives their relative native two-cocycle. For continuous normal invariant
  tensor paths of fixed positive dimensions, with continuous actual left action caps,
  it proves equality of their endpoint relative classes. Continuous right caps are not
  required. The continuous left caps remain a stated intermediate hypothesis.
- `ControlledZClosedFusionObstruction` proves that no fusion caps of the fixed combined
  family give exact letterwise closed reconstruction. This remains impossible after
  every positive physical blocking length: the distinct zero/one diagonal letters of
  the squared controlled-Z generator are idempotent, so their positive powers remain
  distinct, while reconstruction through the identity label would identify them.
  Thus neither different caps nor mere blocking repairs this particular closed-fusion
  premise. The theorem does not exclude a different admissible symmetry embedding.

These are 12 additional public declarations in four proof modules (413 Lean lines).
The campaign now has 81 public declarations in eleven proof modules. All 12 new
statements have Blueprint entries that state their actual restrictions. No physical
Hamiltonian-path conclusion is claimed from supplied reduction data.

### Validation and integration evidence

The four-module package build passes (18,991 jobs in its focused transitive closure),
and each source passes direct strict elaboration with automatic implicits disabled,
synthesis depth 3, standard Mathlib linters and warnings as errors. A temporary audit
verified the 12 public declarations have foundational dependencies contained in
`{propext, Classical.choice, Quot.sound}`; the audit source was removed. Pinned Lean,
QICLean and prebuilt Mathlib artifacts were reused; no Mathlib Lean source was rebuilt.
Generated imports, text style, Blueprint source synchronization/roles, pinned formatting,
reader-facing prose and all 308 paper-gap references pass. The generated declaration
list was refreshed before the source synchronization check; it is not a source artifact.
This is focused local validation, not a complete library or compiled Blueprint acceptance.

At frozen head `65a98e13`, the hosted Lean job
`https://github.com/LionSR/TNLean/actions/runs/43787527913/job/133042789832` passed the
full 32,373-job library build, strict changed-source passes, text style and compiled
Blueprint/paper-gap declaration checks. Both independent Codex and Claude source reviews
found no mathematical blockers at that head. The Blueprint web/PDF jobs were still
running when the next repairs were prepared, so complete CI is not claimed. Four
Copilot style threads are handled by explicit Kronecker entries, bit-case character
multiplication, a documented proof-scoped transparency setting, and separated references.
Any expanded or repaired head requires fresh final-head checks and independent review.

The local full-web command for the frozen head returned zero, but emitted a reflectbox
Jinja-template warning and parent-node diagnostic messages. It is not counted as a
successful complete-render validation. The hosted render remains authoritative and must
finish successfully; no occupied diagram or cochain sources were changed to suppress it.

### Remaining physical bridge and coordination

#10626 was notified before work on the additional consumers. Its prerequisite order and
workflow approval gate are preserved; its branch and occupied files remain untouched.
The new consumers must be included in the owner's eventual coefficient-API migration.
The tactic pattern scan found no new pattern requiring a custom tactic. The nonzero
entry/quotient argument is proved once and reused for action symbols, rather than copied.
The separately owned global tactic ledger was left intact.

The remaining physical work is to construct suitable continuous local action reductions
from an independent physical path, address changes of minimal state bond dimension, and
prove the connection to the source's allowed symmetric gapped paths. A GLM23 route must
construct and verify an alternative admissible arbitrary-boundary symmetry embedding;
the unchanged combined family and its positive blockings cannot satisfy exact closed
fusion. These remain mathematical blockers, not completed classification results.

### Consolidation checkpoint

The reviewed coefficient comparison now scopes its transparency option to its proof,
with the pinned semireducible bit/bond identification explained. The character's
homomorphism law uses the two bit cases, preserving its original physical formula;
the Kronecker proof names the entry formula explicitly, and the adjacent references
are separated. All four touched Lean sources pass direct strict elaboration.
The continuation and review repairs are consolidated into #10686. Upstream main
`3d3507f93fdf6fa52db553cacf30b5df4e60eaa7` is integrated; its intervening changes
are campaign metadata/tooling, not Lean or dependency-pin changes. Earlier-head green
checks and reviews remain historical evidence only. The resulting expanded head must
pass its own complete checks and reviews before merge.

The integrated eleven-module focused build passes (19,109 jobs). In an isolated
review worktree the repaired seven-module closure also passes (19,077 jobs); its
slowest changed modules take 23 seconds when built without competing strict checks.
These are focused builds, distinct from the frozen head's hosted full-library build.

Final integrated checks: all eleven sources pass direct strict elaboration and all
81 public declarations pass the standard foundational-dependency audit. The temporary
audit source was deleted. The frozen head's hosted PDF job failed with TeX errors.
A focused compilation of the actual relative-class subsection reproduced undefined
`\Q` commands at both rational-coefficient references. Both now use `\mathbb{Q}`.
The relative-class and new reduction-path subsections compile together as five XeTeX
pages without a TeX error. This is a focused typesetting check, not complete-volume
acceptance. The expanded head still requires its own full hosted Lean, web and PDF
checks, fresh independent reviews and the applicable approvals. No merge occurred.
