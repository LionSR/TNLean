# Original two-site-blocked condensation symmetry

The remaining original-family boundary of old issue #8041 is proved in
`TNLean/MPS/Examples/AnomalousCondensation/Z2Z2BlockedAnomaly.lean`.
This is a specific constructed example, not a classification of tensors.

## Source and ownership

Original validated base: `6da5dd6c42ae8a911097290fac25b673286cd1ae`.
Publication integration base: `7137c7c7452f91c21ebdd7283536fe09939fd62f`.
The original checkpoint is retained locally. The public commit uses verified
noreply attribution; its production proof is byte-identical to that checkpoint.
The issue and all eight comments were reread, and the 67 returned open PRs
were inspected before edits. No matching active implementation was found.
The last issue comment explicitly identifies the remaining original-family
boundary. Arbitrary Klein detector completeness and the dressed-family class
identification were already on main and were reused, not reproved.

Source: `Papers/2203.12563/REsubmission.tex`, lines 1845–1886. The source
specifies the type-II cocycle and its detector table. These explicit two-qubit
representatives and compression witnesses are repository constructions, not
literally printed source tensors. The associator convention comes from
arXiv:2502.20257, the display preceding `eq:3-cocycle`.

Owned files:

- `TNLean/MPS/Examples/AnomalousCondensation/Z2Z2BlockedAnomaly.lean`
- `TNLean/MPS/Examples/AnomalousCondensation.lean` (generated import)
- `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex`
- `docs/paper-gaps/glm23_z2z2_anomaly_detector_scope.tex`
- `docs/tactic_patterns.md`
- this audit

No generic action-blocking or clock-anomaly file was edited. Imports remain
acyclic: the new leaf imports the existing anomaly calculation and blocking
APIs; only its generated parent aggregator imports the new leaf. Toolchain,
manifest, and dependency pins are unchanged.

## Exact theorem boundary

`blockedTensor g` is `MPOTensor.blockTensor (symTensor (kleinEquiv g)) 2`.
One blocked site is two original physical sites. The original factor is
`lambda(g,h)^N`, with `lambda(g,h)=(-1)^(g1*h2)`; its square is one.
`blockedFamily_isNormalRepresentation` proves actual normality and exact
operator multiplication on every nonempty blocked ring. Identity and inverse
laws are also proved. `raw_odd_square_ne_identity` retains the original
odd-ring obstruction: `U_xy^2 = -U_e`, hence `U_xy^2 != U_e`.

`blockedXFusionData`, `blockedXyFusionData`, and `blockedYFusionData` give
actual fusion witnesses on the three cyclic restrictions. The square
reductions are transported through physical blocking and doubled-index
relabeling. The original `xy` square targets `-M_e`; blocking cancels exactly
`(-1)^2`. The actual raw triple letters satisfy the two tree identities with
signs `+1` for `x` and `-1` for `xy`. Integer arithmetic proves these identities
on the sixteen raw letters, followed by right multiplication on words and
physical blocking. No blocked-matrix enumeration or inference from mere
exactness is used.

For every `fd : blockedFamily.FusionData`,
`omega_blockedFamily_cohomologousTo_kleinCocycle` proves
`CohomologousTo fd.omega kleinCocycle`. There is no normalized-gauge premise.
The three computed detectors are `(+1,+1,-1)`; the existing completeness
result converts those actual computations into class equality.
`not_isTrivialGaugeClass_omega_blockedFamily` proves nontriviality for every
fusion choice. Existence of a fusion choice follows from the proved normal
representation, and is checked in the boundary regressions. No anomaly class
of an exact representation is assigned to the raw odd-ring family.

## Independent native review

A separate native agent reviewed the source, original tensors, compression
witnesses, all new proof bodies, and the Blueprint/gap-note claims. It also
independently checked the two nonzero raw triple-letter matrix identities.
Its final read-only review passed for source SHA256
`68e62b1bfccd7dd1acef1b7dc7c9d7425de22754884230cabb676105fbedabc2`.
No hidden strengthened hypotheses, dressing substitution, circular premises,
or mathematical/source-hypothesis blocker was found. The reviewer did not
rerun Lean; the following execution evidence is separate.

## Original-checkpoint executed validation

Lean commands used the repository-pinned Elan toolchain and matching
prebuilt Mathlib cache.

- The Mathlib checkout matches manifest revision
  `c55e6e786f49471c72fbddbec5415808896aec1e`; prebuilt `Mathlib.olean` exists.
  `lake exe cache get` reported no files to download and 8943 artifacts
  already decompressed. No Mathlib source build was started.
- The prerequisite targeted build of `Z2Z2AnomalyClass`,
  `MPDO.PhysicalBlocking`, and `Core.ReductionBlocking` passed (9355 jobs).
- `lake build TNLean.MPS.Examples.AnomalousCondensation.Z2Z2BlockedAnomaly`
  passed (9356 jobs). Final changed-module compilation took 21 seconds,
  below the repository's 25-second warning and 50-second error thresholds.
- Strict elaboration of the production module passed without diagnostics,
  using `-DautoImplicit=false -DrelaxedAutoImplicit=false`
  `-Dpp.unicode.fun=true -DmaxSynthPendingDepth=3`
  `-Dlinter.mathlibStandardSet=true -DwarningAsError=true`.
- Fourteen temporary actual-name boundary regressions passed with the same
  strict flags: one blocked site versus two raw sites; existence of fusion
  data; odd raw length one and general odd anticommutation; blocked identity,
  inverses and arbitrary multiplication; all three cyclic detectors;
  all-fusion class equality and nontriviality; arbitrary-choice cohomology
  and detector independence. No persistent Lean fixture was added.
- Transitive `#print axioms` checks of all 25 new public declarations found
  only `propext`, `Classical.choice`, and `Quot.sound`. The temporary audit
  resolves the actual compiled declaration names, including all Blueprint
  references to new declarations. No placeholder or extra foundational assumption is present.
- Generated import checks passed (88 aggregators, 4585 production modules).
  Blueprint/source synchronization, duplicate-tag checks and reverse coverage
  for the new module passed. All new public declarations have Blueprint
  references. The modified chapter has no role-transform changes.
- Import-generator tests (11), Blueprint scanner checks (5), and Blueprint
  role tests (8) passed. Reader-facing prose, numbered-module policy,
  changed-directory module-size policy, tactic-pattern scan and whitespace
  checks passed. Pinned `latexindent` 3.24.7 formatted both changed TeX files.

## Publication integration verification

The production proof is byte-identical on the publication integration base.
A separate native read-only review passed the exact six-file resolved diff;
upstream changes and the existing tactic-ledger entries are preserved.
The current-base targeted build, strict production elaboration, fourteen
boundary regressions, and all twenty-five foundational-dependency/export
checks passed. Generated imports are current (89 aggregators, 4642 production
modules). The import-generator, Blueprint scanner, and Blueprint role tests
passed. Complete changed-file privacy scanning and high-confidence credential
scanning of the tracked tree found no candidate secrets or machine-specific
paths in the changed files. Public author and committer attribution use the
noreply identity verified from existing public repository commits.

## Validation limits and remaining nonmathematical blockers

The global Blueprint role check fails on four pre-existing mismatches in
`ch35_aklv_energy_truncation.tex`: three theorem environments and one prose
reference. That file is byte-identical to the refreshed base; the changed
Z2Z2 chapter passes its role transformation. No unrelated repair was made.

The gap-note PDF attempt failed because `dsfont.sty` is unavailable. Full
Blueprint web/PDF rendering and canonical `leanblueprint checkdecls` were not
run; `leanblueprint` is not installed. The full repository root and generated
Examples aggregator were not compiled. Hosted CI was not run. These limits
do not change the successful targeted strict Lean and foundational-dependency checks.

No mathematical blocker remains for the original two-site-blocked family
boundary stated above. Publication integration and its separate checks are
recorded in the draft pull request. Full-root compilation, canonical Blueprint
validation, and hosted acceptance remain separate gates.
