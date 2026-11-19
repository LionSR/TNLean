# Arbitrary TI tensors and measurement preparation (#10572)

Base: `7e8438a32f1f0435e3acec579a89656de1b3f07b` (main at checkout).
Local branch: `codex/ti-measurement-source-10572`.

At the final overlap recheck, main had advanced to
`c97078480c2a9ce664766914999b1be05a4d4fee` through #10760 and #10767.
Only MPU conjugation, its aggregate, blueprint and campaign/gap notes changed;
none overlaps this branch's files. No merge or rebase was performed. Validation
below is against the pinned checkout base, not this later main.

## Ownership and source audit

- #10572 requests the passage from arbitrary tensors to canonical normal-block
  preparation, with the unrestricted source label
  `thm:ldp_all_ti_measurement_source` as the target.
- Active draft #10759 (`a22bb3c724da2076d128c5e4976685e2d322c85a`)
  owns the primitive expansion at `p = gcd(N,D!)`. No code from that draft is
  copied or assumed. Its finite-length witnesses alone do not give a family
  fixed before N or uniform preparation constants.
- Active draft #10758 (`8febfd0c9c99a905a5a80e0c28f294e7679cf946`)
  treats a different, inhomogeneous high-accuracy obstruction.
- Open preparation drafts #10622 and #10652 own inhomogeneous pair/tree
  constructions. Their proof files are untouched. The only shared paths with
  these four drafts are generated import aggregators.
- Main already has unconditional common-period primitive blocks, CPSV
  canonical-form existence after blocking, phase-class refinement, corrected
  multiplicity/overlap preparation, and double-logarithmic canonical preparation.
  These are reused, rather than re-proved or replaced with extra hypotheses.
- The issue's `References/2307.01696/main.tex` is absent. The source was
  checked at https://arxiv.org/html/2307.01696v2 and against the repository's
  existing source transcriptions and multiplicity/mixed-overlap gap notes.
- Read repository `CLAUDE.md`, local conventions, blueprint style, tactic
  development and ledger, and the upstream `lean-conventions` skill. No
  `.agents` directory or AGENTS.md is present in this checkout.

## Mathematical change

`BlockedNormalSectors` derives from an arbitrary `A` a fixed `p > 0` and an
actual `SectorDecomposition P` satisfying `SameMPV₂Pos (blockTensor A p) P.toTensor`.
The common primitive-to-normal reduction is reused through the strengthened
`exists_leftCanonical_cpsvCanonicalFormData_after_blocking`; the old existence
theorem keeps its signature. Its representatives are left-canonical and normal, and distinct representatives
are not gauge-phase equivalent. Copy weights include the phases used in grouping,
so the coefficients are exactly `P.coeff M j`, including multiplicities and
possible cancellations. Empty families are allowed.

The next theorem derives positive definite trace-one stationary matrices and
strict eigenvalue bounds for every mixed map. Neither these matrices nor gaps,
normality, canonical form, periods or injectivity are input hypotheses.

The logarithmic preparation proof is generalized to a periodic vector with an
arbitrary length-dependent normal-sector expansion. The old repeated-block
statement becomes its specialization, with all eight existing theorem signatures
in that file preserved. The existing double-logarithmic theorem already has this
interface. Both are applied to the derived canonical family.

For each arbitrary A, the new preparation conclusions are:

- some fixed p > 0 and c, independent of M and epsilon;
- M >= 2, 0 < epsilon <= 1, and the blocked periodic target nonzero;
- a unit vector within overlap error epsilon;
- logarithmic depth with measurements followed by a circuit, or
  double-logarithmic depth with measurement rounds;
- circuits on M grouped sites of dimension d^p.

## Remaining mathematics

This is not the unrestricted source theorem. Its original blueprint label keeps
no Lean anchor or verification marker.

1. Compile grouped-site deterministic measurement protocols into the original
   nearest-neighbour physical circuit model with a uniform constant overhead
   depending only on d and p. Preserve branch completeness, normalization and
   overlap under the actual flattening equivalence. This is a circuit theorem,
   not merely the existing blocked MPV coefficient identity.
2. Cover original lengths outside multiples of the one fixed period. A normal
   sector coexisting with a period-two sector prevents simply discarding those
   lengths as zero.
3. A route using #10759 must choose finitely many normal families uniformly for
   the divisors p of D!, before varying N; separate primitive surviving sectors,
   group phase classes, and use a maximum of finitely many preparation constants.
   The existential fixed-length expansion must not be used to let the depth
   constant depend on N. The original-site compilation in item 1 is still needed.

## Tactic-pattern check

The common-period primitive-to-normal extraction is shared through the
strengthened constructor in `CPSVAfterBlocking`, preserving its old theorem. The irreducible-channel stationary-matrix
construction occurs here and in `CanonicalFixedPoint` (two occurrences). This stationary-matrix selection remains a candidate for a shared result
at a third occurrence; no new custom tactic is introduced. The scoped pattern scan found no new repeated tactic block
at its promotion threshold. The central ledger is already edited by active
#10759 and #10758; this dated record preserves their ownership.

## Verification

- Focused `lake build TNLean.MPS.Preparation.ArbitraryTensorAfterBlocking`
  passes: **19,209 jobs**. It includes the canonical constructor, sector
  construction, generalized logarithmic preparation and both final results.
- All four edited proof modules pass direct strict elaboration with automatic
  implicits disabled, synthesis depth 3, standard Mathlib linters and warnings
  as errors. The first sector attempt caught dependent elimination on a
  dimension equality; the final proof uses Mathlib's `eqRec_eq_cast`, without
  changing the statement.
- Local `#print axioms` for both sector results and both preparation results
  reports only `propext`, `Classical.choice`, and `Quot.sound`. The temporary
  audit source is removed after the check; no Lean fixtures are added.
- Blueprint source synchronization with duplicate-tag checking, role checks,
  and pinned latexindent checks of the three edited TeX files pass.
- Repository-wide `lake exe lint_style` passes.
- Import-layer, module-size, added-prose, integrity-token, generated-import and
  whitespace checks pass. All eight old theorem signatures in
  `OverlappingMeasurementPreparation` are unchanged. Its generalized proof is
  exactly the old proof with the declared MPV-expansion substitutions.
- `lake build TNLean.MPS.CanonicalForm TNLean.MPS.Preparation` passes:
  **20,113 jobs**.
- The full print-volume check `scripts/check_blueprint_pdf_compiles.sh` passes:
  **3,446 pages**, no TeX errors, expected latexmk status 12 for unsettled
  first-pass references. This is a single-pass typesetting check, not a fully
  settled bibliography or reference build.
- Full `leanblueprint web` rendering was stopped after more than 33 minutes
  while still rendering earlier chapters. It is **not certified**. Its initial
  parse also predates the final prose/verification-marker edits.
- A full-root `lake build TNLean` and full-root blueprint `checkdecls` were not
  run; the new declarations were kernel checked and included in the axiom audit.
- An early strict check of the Preparation aggregator ran before dependencies
  finished and reported missing object files. The completed aggregate build
  resolves that build-order issue. The final rerun of
  `python3 scripts/ci_lean_checks.py strict --base 7e8438a32f1f0435e3acec579a89656de1b3f07b`
  passes **all six changed Lean files**, including both aggregators. The aggregate
  build was also repeated successfully after the final module-docstring edit.
- Pinned prebuilt Mathlib artifacts were downloaded and `Mathlib.olean` verified
  before every build. The focused build log contains **zero Mathlib Lean source builds**.
  The style executable links native objects from cached Mathlib artifacts.
  Toolchain v4.36.0-rc1 and all dependency pins are unchanged.

Prepared locally with OpenAI Codex. No push, PR, merge or external message was made.

## Compatibility adaptation after #10748 (2026-11-17)

The original branch `codex/ti-measurement-source-10572` and commit
`85a48813cbb7abacd164b0a566a09461b53865a8` are preserved unchanged.
The scratch branch `codex/ti-measurement-source-10572-kraus` starts at current main
`9077c2d1e0aee70ad14df4f6ae85acc71439c9cb`, including merged #10748
(`52b6f7235`) and #10743. Cherry-picking the original commit produced
`5cdab8082` without conflicts.

The actual same-file overlaps in `CPSVAfterBlocking` and
`OverlappingMeasurementPreparation` merged cleanly: retain main's selective
`open Kraus (blockPhysDim blockTensor)` in both, and just one existing
`variable {d D : ℕ}` in `CPSVAfterBlocking`. The two new modules,
`BlockedNormalSectors` and `ArbitraryTensorAfterBlocking`, now also selectively
open these Kraus names. Compared with the original campaign commit, each of
these four proof files differs by exactly that one additional open line. No
statement, proof body, assumption, or mathematical scope changes.

The original verification above describes the old base. Fresh validation of the
scratch branch is recorded below; no original-site compilation or all-length
coverage is claimed by this compatibility adaptation.

Fresh validation on the scratch branch:

- `lake build TNLean.MPS.CanonicalForm TNLean.MPS.Preparation` passes
  (20,113 jobs), including both new final preparation results.
- `python3 scripts/ci_lean_checks.py strict --base 9077c2d1e0aee70ad14df4f6ae85acc71439c9cb --jobs 2`
  passes all six changed Lean files, including both aggregators.
- Repository-wide `lake exe lint_style`, import-layer and pass-through checks
  pass. A textual comparison verifies that all four affected proof files match
  the original commit exactly after removing their one additional Kraus open.
- Blueprint source synchronization and duplicate-tag checking pass after
  regenerating the ignored `blueprint/lean_decls` index. The initial check found
  142 stale and 289 missing index entries from the old checkout, with no source
  reference or duplicate-tag failures; the regenerated-index check is clean.
- Whitespace checks pass. No toolchain or dependency pins changed. Full-root
  Lean builds, blueprint `checkdecls`, and web/PDF rendering were not rerun for
  this namespace-only adaptation.

The remaining mathematical gaps listed above are unchanged. No push, PR, merge
into main, or external message was made. The original campaign branch is intact.

## Integration with merged #10761 (2026-11-17)

The previously tested base `9077c2d1e0aee70ad14df4f6ae85acc71439c9cb` does **not**
contain #10761: `git merge-base --is-ancestor a1027eb025c82bacc3836eeff48b5c05eb1d74e8 9077c2d1e0aee70ad14df4f6ae85acc71439c9cb`
returns 1. Its QICLean `rev` and `inputRev` are both
`603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac`.

A separate branch `codex/ti-measurement-source-10572-qiclean` starts at fetched
main `612f8998752998486c6e080a427c65dc6a6847e7`. That base contains merged
#10761, `a1027eb025c82bacc3836eeff48b5c05eb1d74e8` (ancestry exit 0).
Its manifest `rev` and `inputRev`, lakefile requirement, and the checked-out
QICLean dependency are all `e9cc1cc6cd52c6dfc27d7b3aab4b1ba39ea7ed19`.

The campaign and Kraus compatibility commits cherry-picked cleanly as
`58072406a` and `1d16b5080`. Both previous branches remain unchanged. All six
campaign-changed Lean files were checked against the eight module paths
removed by #10761: no stale direct imports were found. Main already reconciles
the moved gate/support imports in dependencies. The four campaign proof
modules are byte-for-byte identical to the previously tested Kraus scratch
head `e62c58d647fbf3bd738e5da1466d65e15fdfb4e6`; no proof or scope edits were needed.

Fresh #10761 integration validation:

- `lake build TNLean.MPS.CanonicalForm TNLean.MPS.Preparation` passes
  (20,115 jobs), including both arbitrary-tensor preparation results.
- `python3 scripts/ci_lean_checks.py strict --base 612f8998752998486c6e080a427c65dc6a6847e7 --jobs 2`
  passes all six changed Lean files.
- Import-layer and whitespace checks pass. No pins were changed relative to the
  new base. The build checked out and used the required QICLean revision.
- No full-root build or blueprint rendering/checkdecls rerun was performed for
  this integration. The same original-site and all-length gaps remain open.

Only this audit was added after the clean cherry-picks. No push, PR, or merge
into main was made.

## Review preparation (2026-11-17)

After explicit authorization to publish the completed campaign for review, the
review branch `codex/ti-measurement-source-10572-review` was based on fetched main
`55cab8718dfb268fe2d80afa755c66734648d154`. The only intervening main change was
#10697; the three integration commits cherry-picked without conflicts. The four
proof modules are unchanged from validated integration head
`76f1fa3c6e7290e496a5a68c6d9a92ffd58a3177`. Original branches remain preserved.

The current open-PR search found no duplicate for #10572. File-list checks of
#10759, #10758, #10617, #10618, #10622, #10652 and #10656 found only generated
aggregate overlaps, with no shared proof or blueprint edits. The contribution
remains a fixed-blocking theorem; it does not close #10572.

On review base `55cab8718dfb268fe2d80afa755c66734648d154`, both aggregates pass
(20,115 jobs), as do all six strict changed-source checks, repository-wide style,
import layers, blueprint roles, blueprint source synchronization with duplicate
checking, and whitespace checks. QICLean remains pinned and checked out at
`e9cc1cc6cd52c6dfc27d7b3aab4b1ba39ea7ed19`. Full-root Lean and compiled blueprint
checks/web/PDF rendering were not rerun on this review base. The PR is prepared
as a draft pending hosted CI and mathematical review. Historical no-publication
statements above describe the earlier stages before publication was authorized.

## External auto-fix and latest-main reconciliation (2026-11-17)

Remote #10814 advanced externally from `8eb78de8e` to
`bea9be99753dfe170a8756910503f49e29dac66f`. Its commit and PR comment identify
Claude's auto-fix of the old `sitewisePhysicalMatrix` API in
`MPU/Examples/ShiftTildeSymmetricPhases`. The same repair subsequently landed on
main through #10813, merge `95f5970db777f4c2fd1e16d1ac36281b84f46aff`.

The reconciliation starts from the external head and merges that exact main,
preserving the external commit as an ancestor. The only conflict is three proof
details in `ShiftTildeSymmetricPhases`; resolve them to the exact merged #10813
file, whose hosted build passed. The tensorPower migration is retained, without
carrying a second version of the same unrelated repair in the campaign diff.
The campaign's four proof modules and its mathematical scope remain unchanged.

Run `44079410999` for the external head is completed with `action_required`,
triggered by `github-actions[bot]`, with zero jobs and zero check runs. The API
exposes no more specific approval reason; this is not a Lean elaboration result.
No workflow approval, rerun, policy change, or merge of the PR was requested.

Local reconciliation validation passes: the two campaign aggregates plus
`TNLean.MPS.MPU.Examples.ShiftTildeSymmetricPhases` build (20,387 jobs); strict
checks against main `95f5970db777f4c2fd1e16d1ac36281b84f46aff` pass all six
campaign Lean files, and the reconciled MPU file separately passes the same
strict flags. Its contents match main byte-for-byte. All four campaign proof
modules match reviewed head `8eb78de8e` byte-for-byte. Whitespace checks pass.
Full-root and blueprint builds were not rerun locally in this reconciliation.
Remote main and PR head were rechecked unchanged before the normal fast-forward
push. The existing action-required run is left untouched; fresh-head hosted
acceptance remains required. This pass does not merge or mark ready the PR.
