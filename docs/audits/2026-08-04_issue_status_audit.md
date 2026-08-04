# Issue status audit — 2026-08-04

Scope: all 145 open GitHub issues. Method: per-issue dossiers (body +
stale-citation findings from `scripts/audit_stale_issues.py` against current
main), then a per-issue repo-state deep dive (sorry sites, declaration
existence, blueprint `\leanok` entries, merged PRs). Read-only: no issues
were edited or closed. Raw exports in `tmp/issues_open.json`,
`tmp/issues_audit.json`, `tmp/issue-audit/` (gitignored scratch).

Tally: **11 closeable**, **3 superseded** (+2 consolidation candidates),
**7 need splitting**, **24 trackers need body updates** (6 up-to-date),
**47 open non-tracker issues are not referenced by any tracker**.

## 1. Closeable now (work verified on main)

| Issue | Evidence |
|---|---|
| #631 sharp rank-one Neumark extension | PR #5109 merged 2026-07-29. `POVM.exists_orthonormal_basis_restriction_of_rank_one` (`TNLean/Channel/POVM/RankOneNaimark.lean:145`), sorry-free, blueprint `thm:sharp_rank_one_naimark` `\leanok`. |
| #2318 W state as MPS + lower bound | Item (a) done by PR #2946: `TNLean/MPS/Examples/WState.lean` sorry-free. Item (b) explicitly delegated to open #2947. Close with pointer to #2947. |
| #2470 PEPS RegionInsertionTransfer from SameState | Discharged via the coherent-frame route: `exists_regionEdgeGauge_of_blockingData` (`TNLean/PEPS/CoherentFrameInstance2.lean:174`) → `regionInsertionTransfer_of_coeffTransfer` (`RegionBlock/RegionReconcile.lean:323`). Closure comment should cite the alternate route; one docstring at `RegionReconcile.lean:310-318` is now stale. |
| #2616 PEPS torus reference blocking datum + transport | All three deliverables exist (`torusHorizontalReferenceBlockingDatum`, `regionInsertedCoeff_translate_coeffIdentity` at `RegionTransferCovariance.lean:139`, `transportBlockingDataAlong_redBlue`); feeds `fundamentalTheorem_normalTorusPEPS_unconditional` (`TorusFundamentalTheorem2.lean:298`, `\leanok`, sorry-free). |
| #3965 Wolf Ch1 conditional-expectation classification | PRs #4138/#4147. `StarSubalgebra.exists_block_densities_of_positive_retraction` (`TNLean/Channel/PositiveConditionalExpectationDirectSum.lean:672`), blueprint `thm:positive_retraction_finite_star_algebra` `\leanok`, scope restriction resolved per `docs/paper-gaps/wolf_prop1_5_one_factor_scope.tex`. |
| #4065 Disable per-run lake cache in CI | `.github/workflows/auto-fix.yml:226` passes `use_github_cache: false`; all local `lean-env-action` calls carry `use-github-cache: false`; `gh api .../caches` shows no `lake-*` entries. |
| #5086 tenkz plane frame with declared basis | Label `all-resolved`, bot reports 3/3 sub-issues closed; acceptance verified in tree (`rmp-iii-a-ghz-state`, `fig21d_cubic` respelled, kernel guards `plane-rise-low`/`plane-slant-band` at `tenkz-kernel.code.tex:4578,4594`). Caveat for closer: `planes-interleave` guard still lattice-tier only. |
| #5422 Wolf Prop 6.2 (TP peripheral Jordan blocks) | PR #5431 merged 2026-08-04. `IsPositiveMap.peripheral_Jordan_trivial_of_tracePreserving` (`TNLean/Channel/Peripheral/JordanBlocks.lean:222`), blueprint `thm:peripheral_jordan_trivial` `\leanok` with scope restriction stated. Unital half already split to #5447. |
| #5428 Wolf Cor 6.8 stationary density basis | PR #5431. `IsPositiveMap.exists_stationaryDensity_basis_of_fixedPointsSubmodule` (`TNLean/Channel/FixedPoint/StationarySpan.lean:206`), blueprint `cor:stationary_density_span` `\leanok`. |
| #5429 Blueprint entries for Kato CPSV capstone | PR #5440: `thm:kato_deformed_mpdo_cf_sal_capstone` (`blueprint/src/chapter/ch21_mpdo_rfp_foundations.tex:293-343`) with `\lean{}`/`\leanok`; decls sorry-free at `TNLean/MPS/MPDO/KatoDeformedRFPObstruction.lean:579,852,896`. |
| #5444 Rescaling-stability block-rescaling fix | PR #5448 merged 2026-08-04: `oneLabelCoeffs_rescaling_stable_not_lengthIndependent` (`TNLean/MPS/MPDO/RescalingStableLengthDependentRFP.lean:242-272`) implements exactly the prescribed fix. |

Closeable candidates needing maintainer judgment:

- **#2738** (torus normal PEPS FT tracker): if it tracks only the Theorem-3
  torus form, it is closeable — `fundamentalTheorem_normalTorusPEPS_unconditional`
  is `\leanok` and sorry-free. Otherwise update its body with the six open
  route issues (see §4).
- **#622** (p-refinement/p-divisibility): now coextensive with #664 (its own
  body says "the only active child is #664"). Either retitle `Tracking:` or
  close as redundant.

## 2. Superseded / consolidation candidates

- **#2750** → superseded by #2787. The prescribed route was mathematically
  refuted in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex:522-540`
  (2D end windows touch bond `e` with one endpoint; per-window families are
  vectors, never a square-matrix span). Geometry prerequisites landed.
- **#2781** → superseded by #2787. The Skolem–Noether back end is landed
  (`edgeGaugeFromInsertionAlgebraIsomorphism`,
  `exists_regionConjCoeffIdentity_of_transfer` at `TorusWindowMult.lean:150`);
  the live residual (staircase multiplicativity) is owned by #2787/#2780.
- **#4943** → superseded by #5086. Maintainer already flagged it as
  conflicting with the 1.0 contract; the contract route (`frame={flat,
  basis={...}}`) landed.
- **#952** ↔ **#5164**: #952's only remaining content is exactly #5164's task
  (the Friedrichs-bound instantiation for MPS excitation kernels). Close
  #952 as superseded by #5164, or cross-link explicitly.
- **#2660** ↔ **#4872**: #2660's definitions landed (PR #2978); its remaining
  endpoint-realizability comparison is exactly #4872's Theorem 1 scope.
  Consolidate to avoid double-tracking.

## 3. Needs splitting

- **#3963** (Wolf Ch1): three independent propositions — (a) Schmidt
  decomposition (infrastructure nearly ready), (b) quantum steering (zero
  formalization), (c) maximal ensemble weight (zero formalization).
- **#3966** (Wolf Ch1): (a) CP-from-positivity (proved key lemma exists at
  `Schwarz/PositiveOnAbelian/Characterization.lean:442`; needs source-faithful
  statement or documented restriction + blueprint entry), (b) operator-system
  extension (greenfield).
- **#2148**: cluster-state bullet fully done (`ch15_examples_cluster_state.tex`
  `\leanok` ×3); split off the SO(3) continuous-cohomology piece
  (needs continuous group cohomology; gap note exists).
- **#3401**: reduction criterion and Breuer–Hall positivity done; split
  "Breuer–Hall indecomposability (antisymmetric U, d even)" into its own
  issue, then retitle #3401 as tracker or close in favor of #3622/#3623 + new issue.
- **#5406**: coefficient capstone done (PRs #5438/#5448); split the remaining
  gap — `IsMPDO R`, literal CPSV canonical form, `IsRFPViaTS R` — into
  separate issues (module docstring `RescalingStableLengthDependentRFP.lean:40-59`
  lists them).
- **#139** (Wolf Ch6): detach the Thm 6.15 / line-1517 uniqueness theorem
  (explicitly NOT FORMALIZED at `WolfChapter6Index.lean:612`) from the
  four-clause packaging.
- **#3984** (Wolf Ch6): detach the T∞/Tφ Cesaro spectral-projection package
  (item 3; #24 depends specifically on it). Items 2 (TP case) and 4
  (Dirichlet) are done.

Optional: #4847 (P3 dead-edge waves vs P4 MatrixAux split), #4904 (defect 5
folds into #5350's free-tier retirement), #5045 (DOM regression harness vs
renderer fix).

## 4. Tracking issues: concrete body updates

Up-to-date (no action): **#22, #996, #3958, #2289, #2661, #4703**.

- **#19**: minor — drop stale sentence about line-323 CP check awaiting
  confirmation; #3954 now marks it complete (axioms clean).
- **#20**: remove closed #3987 (completed by PR #5430); add open #5437;
  refresh the "none of its 17 theorem-like environments" claim (lines 60/229
  now complete).
- **#21**: notes-only — the "remaining Chapter 5 gap" description predates
  #3973 and #5441.
- **#138**: replace the fully-closed "Open tasks" (#778/#779/#863) with the
  actual open sub-issues #3974, #3975.
- **#992**: fix wrong "Chapter 1 closed" claim (#19 is open/reopened); add
  #3958 as the Ch8 tracker.
- **#995**: move #3972 (closed via PR #4043) from partial to complete.
- **#3954**: fix dangling refs to closed #3972/#3983/#3985 — point Ch6
  lines 1143/1204 at open #5427/#5428; note the Ch5 line-198 Schwarz
  *equality criterion* is now tracked nowhere (PR #5424 delivered only the
  conditional inequality, #5441 covers the unconditional inequality only) —
  an issue should be (re)opened for it; add #5422/#5423/#5427/#5428/#5437/#5441
  to the issue trees; refresh the aggregate counts.
- **#82, #619, #1809**: #5342 is closed but still listed as active in all
  three; #1809 also lists closed #5407 as active. Add #5387 to #82/#619.
- **#190**: remove closed #2971/#2633 from active leaves; add #5164; body
  claims `parentHamiltonianES_gapped` is on main but the declaration no
  longer exists — verify.
- **#232**: remove closed #5407/#2380 from active threads; add open
  #5420, #5429, #5434-#5436, #5444, #5445, #5449.
- **#1252**: severely stale — 24 of 25 checklist items are closed (only #1373
  correctly open); closed #128 still described as an active strand; the
  current front (#2449, #2450, #2606, #2691, #2738, #2723, #3371, #3478) and
  follow-ups (#2470, #2616, #2707, #2720, #2750, #2780, #2781, #2787, #2921)
  are absent.
- **#1373**: closed #1360-#1368/#1374-#1376/#1256/#1257 still listed; add
  #2449 (Phase C), #2450 (Phase D), candidates #2606/#2691.
- **#1447**: acceptance criterion 2 (unconditional `∑ c_j λ_j^n`) is not a
  true statement with Jordan blocks — incorporate #1809's correction
  (allow `n^k λ^n` terms or a diagonalizability hypothesis).
- **#2147**: add cross-references to #2661, #2148, #2289; record closed #2283
  as done.
- **#2320**: #2319 closed but still `[~]` (point residual at #460); umbrella
  #903 closed; consider adding #4872/#2660.
- **#2738**: add the six open route issues #2720, #2616, #2750, #2780, #2781,
  #2787 (see §1 for the closeable candidate question).
- **#4163**: add #4708 (manual rewrite is a de-facto precondition).
- **#4164**: link the five tasks to their decomposing sub-issues
  #5352-#5357.
- **#4183**: refresh Working agreements (order #4393/#4395/#4394 all closed;
  #4161 landed; #4156 backlog pointer dead); the new wave #5347-#5350, #5360,
  #5362, #5363, #5383, #4761, #5045 is referenced by no tracker.
- **#4529**: annotate demolition candidates (4/6 closed: #4563/#4566/#4567/#4568;
  only #4564/#4565 open); the `SameStateBridgeHyp` reference is dead (zero
  matches in TNLean/); confirm #4522 is attached.
- **#4709**: #5135 closed one day after the last refresh; add the untracked
  wave #5347-#5350, #5360, #5362, #5363, #5383; the #4156 backlog it points
  to is closed.
- **#4866**: add #4847; note the ranked queue predates PR #4864 and should be
  re-measured.

## 5. Open issues not referenced by any tracker (47) — suggested homes

- Wolf coverage: #5422, #5423, #5427, #5428, #5447 → **#3954** (Ch6 tree);
  #5437 → **#20** + **#3954**.
- RFP/MPDO: #5420, #5429, #5434, #5435, #5436, #5444, #5445, #5449 → **#232**.
- PEPS: #2470, #2616, #2707, #2720, #2921 → **#1252**; #2750, #2780, #2781,
  #2787 → **#2738** (or #1252); #4522 → **#4529**.
- 1708.00029: #5387 → **#82** + **#619**.
- SPT/RMP: #2660 → **#2320**; #4872 → **#2320** (+#2147); #1529 → **#1809**.
- tenkz: #4761, #5347, #5348, #5349, #5350, #5360, #5362, #5363, #5383 →
  **#4709** (and/or #4183); #5352-#5357 → **#4164**.
- Lean infra: #4847 → **#4866**; #4037, #4564 (already under #4529), #5045 →
  judgment call (#5045 fits no current tracker; #4183 adjacent).
- #4065 needs no tracker (closeable, §1).

## 6. Active issues with PRs in flight (do not touch)

- #3616 ← open PR #5446 (rectangular generic normal form; closes it).
- #3973 ← PRs #5433/#5442; #3976 ← PR #5443; #3396 work in flight unmerged.

## 7. Caveats

- Verdicts rest on source/blueprint/PR inspection; no `lake build` or
  `leanblueprint checkdecls` was run during this audit.
- The worktree holds uncommitted in-flight tenkz migration work (dirty
  `tests/tenkz/rmp/*`, `dimension-ownership.json` 708→478, kernel edits) —
  an agent mid-slice on #5347/#5348/#5350. Verdicts above are against merged
  main; landing that work would partially advance those three issues.
- `scripts/audit_stale_issues.py` produced some false positives (module paths
  flagged as declarations, literal `leanok` string); its flagged set was used
  only as a triage aid.
- Standing issues #4158 (simplification gate) and #4761 (PR review triage)
  are open by design and should stay open.

## Appendix: full status table (145 issues)

CLOSEABLE (11): #631, #2318, #2470, #2616, #3965, #4065, #5086, #5422, #5428,
#5429, #5444.
SUPERSEDED (3): #2750, #2781, #4943.

| Issue | Status | Note |
|---|---|---|
| #19 | tracker, needs minor update | §4 |
| #20 | tracker, needs update | §4 |
| #21 | tracker, notes-only update | §4 |
| #22 | tracker, up-to-date | verify #5422-#5428 attached |
| #23 | PARTIAL | stationary-support structure |
| #24 | ACTIVE | depends on #3984 Cesaro package |
| #27 | PARTIAL | Thm 6.14 done; Cors 6.6-6.7 Kraus-only |
| #82 | tracker, needs update | #5342 closed; add #5387 |
| #125 | ACTIVE | |
| #126 | ACTIVE | |
| #138 | tracker, needs update | open tasks fully closed → #3974/#3975 |
| #139 | ACTIVE, split candidate | detach Thm 6.15 |
| #190 | tracker, needs update | add #5164; drop closed #2971/#2633 |
| #232 | tracker, needs update | add 8 new follow-ups |
| #460 | ACTIVE | capstone; sole live leaf is #952/#5164 |
| #619 | tracker, needs update | #5342 closed; add #5387 |
| #622 | ACTIVE, redundant with #664 | retitle Tracking: or close |
| #631 | CLOSEABLE | PR #5109 |
| #664 | ACTIVE | blueprint path renamed ch11b→ch22 |
| #764 | ACTIVE | |
| #765 | ACTIVE | |
| #766 | ACTIVE, needs reframe | cited declaration deleted (statement false); see `docs/paper-gaps/wolf_prop2_11_lorentz_scalar_filtering_gap.tex` |
| #829 | ACTIVE | |
| #952 | ACTIVE, consolidate with #5164 | |
| #992 | tracker, needs update | Ch1 not closed; add #3958 |
| #995 | tracker, needs update | #3972 complete |
| #996 | tracker, up-to-date | |
| #1252 | tracker, severely stale | 24/25 checklist items closed |
| #1373 | tracker, needs update | add #2449/#2450 |
| #1447 | tracker, statement correction | Jordan-block caveat |
| #1529 | ACTIVE | link #1809 |
| #1809 | tracker, minor update | #5342/#5407 closed |
| #2147 | tracker, needs update | add #2661/#2148/#2289 |
| #2148 | PARTIAL, split | cluster done; SO(3) piece open |
| #2289 | tracker, up-to-date | |
| #2318 | CLOSEABLE | remainder is #2947 |
| #2320 | tracker, minor update | |
| #2449 | PARTIAL | |
| #2450 | PARTIAL | |
| #2470 | CLOSEABLE | coherent-frame route |
| #2606 | ACTIVE | |
| #2616 | CLOSEABLE | torus FT discharged |
| #2660 | PARTIAL, consolidate with #4872 | defs landed PR #2978 |
| #2661 | tracker, up-to-date | |
| #2691 | ACTIVE | |
| #2707 | ACTIVE | |
| #2720 | PARTIAL | |
| #2723 | ACTIVE | |
| #2738 | tracker, needs update; closeable candidate | if Theorem-3-only scope |
| #2750 | SUPERSEDED by #2787 | route refuted in gap note |
| #2780 | ACTIVE | |
| #2781 | SUPERSEDED by #2787 | Skolem–Noether landed |
| #2787 | ACTIVE | owns the live residual |
| #2921 | ACTIVE | |
| #2947 | ACTIVE | link #2320 |
| #3371 | ACTIVE | |
| #3394 | ACTIVE | |
| #3396 | ACTIVE | work in flight |
| #3399 | PARTIAL | |
| #3400 | PARTIAL | infrastructure only |
| #3401 | PARTIAL, split underway | Breuer–Hall indecomposability open |
| #3402 | PARTIAL | Prop 3.8 reverse directions open |
| #3616 | ACTIVE | open PR #5446 closes it |
| #3622 | PARTIAL | |
| #3623 | PARTIAL | prerequisite 1/3 done |
| #3954 | tracker, needs update | dangling refs; line-198 equality criterion untracked |
| #3958 | tracker, up-to-date | |
| #3959 | PARTIAL | small |
| #3960 | ACTIVE | |
| #3961 | PARTIAL | |
| #3962 | ACTIVE | |
| #3963 | ACTIVE, split ×3 | |
| #3964 | ACTIVE | |
| #3965 | CLOSEABLE | PRs #4138/#4147 |
| #3966 | PARTIAL, split ×2 | |
| #3967 | ACTIVE | |
| #3968 | ACTIVE | |
| #3969 | ACTIVE | |
| #3970 | ACTIVE | |
| #3971 | ACTIVE | nothing started |
| #3973 | ACTIVE | PRs #5433/#5442 in flight |
| #3974 | PARTIAL | |
| #3975 | PARTIAL | mandated paper-gap note still missing |
| #3976 | ACTIVE | PR #5443 in flight |
| #3977 | ACTIVE | |
| #3984 | PARTIAL, split candidate | 2/4 items done; detach Cesaro package |
| #4037 | PARTIAL | nearly done; ~9 residual suppressions |
| #4065 | CLOSEABLE | CI cache disabled |
| #4158 | ACTIVE (standing) | stays open by design |
| #4162 | PARTIAL | core landed 2026-08-02; checkboxes unticked |
| #4163 | tracker, needs update | add #4708 |
| #4164 | tracker, needs update | link #5352-#5357 |
| #4183 | tracker, needs update | dead backlog pointer |
| #4522 | PARTIAL | link #4529 |
| #4529 | tracker, needs update | 4/6 demolition candidates closed |
| #4564 | PARTIAL | 7 waves landed; small residue in `BNTBlockIntersection.lean` |
| #4565 | PARTIAL | Lean route retired; dormant ch23 blueprint files remain |
| #4699 | ACTIVE | |
| #4703 | tracker, up-to-date | |
| #4708 | PARTIAL | |
| #4709 | tracker, needs update | add untracked wave |
| #4761 | ACTIVE (standing) | 13 live review threads |
| #4847 | PARTIAL | P1/P2/P5/P3-A landed; link #4866 |
| #4866 | tracker, needs update | add #4847 |
| #4872 | PARTIAL | Lemma 1 virtual form exists; blueprint not synced |
| #4904 | PARTIAL | 1/5 defects fixed; defect 5 → #5350 |
| #4943 | SUPERSEDED by #5086 | |
| #5045 | ACTIVE | unaddressed |
| #5086 | CLOSEABLE | all-resolved, verified |
| #5164 | ACTIVE | the live #952 leaf |
| #5343 | ACTIVE | |
| #5344 | ACTIVE | |
| #5347 | ACTIVE | uncommitted in-flight work in worktree |
| #5348 | ACTIVE | idem |
| #5349 | ACTIVE | |
| #5350 | ACTIVE | idem; also moots #4904 defect 5 |
| #5352 | PARTIAL | |
| #5353 | ACTIVE | blocked on #4699/#4708/#4163 chain |
| #5354 | ACTIVE | idem |
| #5355 | ACTIVE | idem |
| #5356 | ACTIVE | idem |
| #5357 | PARTIAL | draft exists in worktree |
| #5360 | ACTIVE | |
| #5362 | PARTIAL | |
| #5363 | ACTIVE | |
| #5383 | PARTIAL | |
| #5387 | ACTIVE | link #82/#619 |
| #5404 | PARTIAL | children #5434-#5436 open |
| #5406 | PARTIAL, split | capstone done (PRs #5438/#5448) |
| #5420 | ACTIVE | link #232 |
| #5422 | CLOSEABLE | PR #5431 |
| #5423 | ACTIVE | |
| #5427 | ACTIVE | Brouwer available in vendored Gametheory dep |
| #5428 | CLOSEABLE | PR #5431 |
| #5429 | CLOSEABLE | PR #5440 |
| #5434 | ACTIVE | |
| #5435 | ACTIVE | |
| #5436 | ACTIVE | |
| #5437 | ACTIVE | link #20/#3954 |
| #5441 | ACTIVE | |
| #5444 | CLOSEABLE | PR #5448 |
| #5445 | ACTIVE | |
| #5447 | ACTIVE | unital half of #5422's scope |
| #5449 | ACTIVE | |
