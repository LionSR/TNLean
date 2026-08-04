# Issue status audit — 2026-08-04

Scope: all 145 open GitHub issues. Method: per-issue dossiers (body +
stale-citation findings from `scripts/audit_stale_issues.py` against current
main), then a per-issue repo-state deep dive (sorry sites, declaration
existence, blueprint `\leanok` entries, merged PRs). Raw exports in
`tmp/issues_open.json`, `tmp/issues_audit.json`, `tmp/issue-audit/`
(gitignored scratch).

**Actions executed 2026-08-04 (post-audit):** 14 issues closed with evidence
comments (11 completed: #631, #2318, #2470, #2616, #3965, #4065, #5086,
#5422, #5428, #5429, #5444; 3 superseded: #2750, #2781, #4943); 12 split
child issues filed (#5465–#5476) with parent cross-link comments; 25 tracker
bodies updated with dated status-refresh sections (#1252's stale checklist
flipped in place, 24/25 items); summary broadcast posted on #1809. Open
issue count: 145 → 131 (before the 12 new split children).

Tally at audit time: **11 closeable**, **3 superseded** (+2 consolidation
candidates), **7 need splitting**, **24 trackers need body updates**
(6 up-to-date), **47 open non-tracker issues are not referenced by any
tracker**.

## 1. Closeable now (work verified on main) — CLOSED 2026-08-04

| Issue | Evidence |
|---|---|
| #631 sharp rank-one Neumark extension | PR #5109 merged 2026-07-29. `POVM.exists_orthonormal_basis_restriction_of_rank_one` (`TNLean/Channel/POVM/RankOneNaimark.lean:145`), sorry-free, blueprint `thm:sharp_rank_one_naimark` `\leanok`. |
| #2318 W state as MPS + lower bound | Item (a) done by PR #2946: `TNLean/MPS/Examples/WState.lean` sorry-free. Item (b) explicitly delegated to open #2947. Closed with pointer to #2947. |
| #2470 PEPS RegionInsertionTransfer from SameState | Discharged via the coherent-frame route: `exists_regionEdgeGauge_of_blockingData` (`TNLean/PEPS/CoherentFrameInstance2.lean:174`) → `regionInsertionTransfer_of_coeffTransfer` (`RegionBlock/RegionReconcile.lean:323`). Closure comment cites the alternate route; one docstring at `RegionReconcile.lean:310-318` is now stale. |
| #2616 PEPS torus reference blocking datum + transport | All three deliverables exist (`torusHorizontalReferenceBlockingDatum`, `regionInsertedCoeff_translate_coeffIdentity` at `RegionTransferCovariance.lean:139`, `transportBlockingDataAlong_redBlue`); feeds `fundamentalTheorem_normalTorusPEPS_unconditional` (`TorusFundamentalTheorem2.lean:298`, `\leanok`, sorry-free). |
| #3965 Wolf Ch1 conditional-expectation classification | PRs #4138/#4147. `StarSubalgebra.exists_block_densities_of_positive_retraction` (`TNLean/Channel/PositiveConditionalExpectationDirectSum.lean:672`), blueprint `thm:positive_retraction_finite_star_algebra` `\leanok`, scope restriction resolved per `docs/paper-gaps/wolf_prop1_5_one_factor_scope.tex`. |
| #4065 Disable per-run lake cache in CI | `.github/workflows/auto-fix.yml:226` passes `use_github_cache: false`; all local `lean-env-action` calls carry `use-github-cache: false`; `gh api .../caches` shows no `lake-*` entries. |
| #5086 tenkz plane frame with declared basis | Label `all-resolved`, bot reports 3/3 sub-issues closed; acceptance verified in tree (`rmp-iii-a-ghz-state`, `fig21d_cubic` respelled, kernel guards `plane-rise-low`/`plane-slant-band` at `tenkz-kernel.code.tex:4578,4594`). Caveat for closer: `planes-interleave` guard still lattice-tier only. |
| #5422 Wolf Prop 6.2 (TP peripheral Jordan blocks) | PR #5431 merged 2026-08-04. `IsPositiveMap.peripheral_Jordan_trivial_of_tracePreserving` (`TNLean/Channel/Peripheral/JordanBlocks.lean:222`), blueprint `thm:peripheral_jordan_trivial` `\leanok` with scope restriction stated. Unital half already split to #5447. |
| #5428 Wolf Cor 6.8 stationary density basis | PR #5431. `IsPositiveMap.exists_stationaryDensity_basis_of_fixedPointsSubmodule` (`TNLean/Channel/FixedPoint/StationarySpan.lean:206`), blueprint `cor:stationary_density_span` `\leanok`. |
| #5429 Blueprint entries for Kato CPSV capstone | PR #5440: `thm:kato_deformed_mpdo_cf_sal_capstone` (`blueprint/src/chapter/ch21_mpdo_rfp_foundations.tex:293-343`) with `\lean{}`/`\leanok`; decls sorry-free at `TNLean/MPS/MPDO/KatoDeformedRFPObstruction.lean:579,852,896`. |
| #5444 Rescaling-stability block-rescaling fix | PR #5448 merged 2026-08-04: `oneLabelCoeffs_rescaling_stable_not_lengthIndependent` (`TNLean/MPS/MPDO/RescalingStableLengthDependentRFP.lean:242-272`) implements exactly the prescribed fix. |

Closeable candidates needing maintainer judgment (left open, commented):

- **#2738** (torus normal PEPS FT tracker): if it tracks only the Theorem-3
  torus form, it is closeable — `fundamentalTheorem_normalTorusPEPS_unconditional`
  is `\leanok` and sorry-free. Otherwise update its body with the six open
  route issues (refresh section appended 2026-08-04).
- **#622** (p-refinement/p-divisibility): now coextensive with #664 (its own
  body says "the only active child is #664"). Either retitle `Tracking:` or
  close as redundant.

## 2. Superseded / consolidation candidates

- **#2750** → CLOSED as superseded by #2787. The prescribed route was
  mathematically refuted in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex:522-540`
  (2D end windows touch bond `e` with one endpoint; per-window families are
  vectors, never a square-matrix span). Geometry prerequisites landed.
- **#2781** → CLOSED as superseded by #2787. The Skolem–Noether back end is
  landed (`edgeGaugeFromInsertionAlgebraIsomorphism`,
  `exists_regionConjCoeffIdentity_of_transfer` at `TorusWindowMult.lean:150`);
  the live residual (staircase multiplicativity) is owned by #2787/#2780.
- **#4943** → CLOSED as superseded by #5086. Maintainer already flagged it as
  conflicting with the 1.0 contract; the contract route (`frame={flat,
  basis={...}}`) landed.
- **#952** ↔ **#5164**: #952's only remaining content is exactly #5164's task
  (the Friedrichs-bound instantiation for MPS excitation kernels). Cross-link
  comments posted on both; not consolidated.
- **#2660** ↔ **#4872**: #2660's definitions landed (PR #2978); its remaining
  endpoint-realizability comparison is exactly #4872's Theorem 1 scope.
  Cross-link comments posted on both.

## 3. Needs splitting — children FILED 2026-08-04

- **#3963** (Wolf Ch1) → #5465 (Schmidt decomposition), #5466 (quantum
  steering), #5467 (maximal ensemble weight).
- **#3966** (Wolf Ch1) → #5468 (source-faithful Prop 1.6 / documented
  restriction + blueprint entry), #5469 (operator-system extension).
- **#2148** → #5470 (AKLT H²(SO(3),U(1)) class via continuous group
  cohomology). Cluster-state and ℤ₂×ℤ₂ AKLT items done.
- **#3401** → #5471 (Breuer–Hall indecomposability, antisymmetric U, d even).
  Reduction criterion and Breuer–Hall positivity done.
- **#5406** → #5472 (`IsMPDO R`), #5473 (literal CPSV canonical form),
  #5474 (`IsRFPViaTS R`). Coefficient capstone done (PRs #5438/#5448).
- **#139** (Wolf Ch6) → #5475 (Thm 6.15 / line-1517 uniqueness theorem).
- **#3984** (Wolf Ch6) → #5476 (Cesàro spectral-projection package; #24
  depends on it). Items 2 (TP case) and 4 (Dirichlet) done.

Optional (not split): #4847 (P3 dead-edge waves vs P4 MatrixAux split),
#4904 (defect 5 folds into #5350's free-tier retirement), #5045 (DOM
regression harness vs renderer fix).

## 4. Tracking issues: body updates — APPLIED 2026-08-04

Dated "Status refresh 2026-08-04" sections were appended to 25 trackers:
#19, #20, #21, #22, #82, #138, #190, #232, #619, #992, #995, #1252, #1373,
#1447, #1809, #2147, #2320, #2738, #3954, #4163, #4164, #4183, #4529,
#4709, #4866. #1252's stale checklist was additionally flipped in place
(24 of 25 items were closed-but-unchecked; only #1373 remains open).

Up-to-date (no action): **#22, #996, #3958, #2289, #2661, #4703** (#22
received a refresh note listing new Ch6 leaves).

The corrections applied per tracker:

- **#19**: line-323 CP check is complete with clean axioms; new sub-issues
  #5465–#5469 recorded.
- **#20**: closed #3987 removed (PR #5430); open #5437 added; stale header
  claim flagged.
- **#21**: notes predated #3973 and #5441; current open wolf-ch5 set recorded.
- **#22**: new Ch6 leaves listed: #5422/#5428 (closed), #5423, #5427, #5447,
  #5475, #5476.
- **#138**: fully-closed task list (#778/#779/#863) replaced by #3974/#3975.
- **#992**: wrong "Chapter 1 closed" claim corrected (#19 open); #3958 added
  as Ch8 tracker.
- **#995**: #3972 marked complete (PR #4043); #5471 added.
- **#3954**: dangling refs #3972/#3983/#3985/#3987 resolved; Ch5 line-198
  Schwarz equality criterion flagged as tracked nowhere (needs an issue);
  new tree additions #5423/#5427/#5447/#5475/#5476/#5437/#5441/#5465–#5469.
- **#82, #619, #1809**: closed #5342 (and #5407 for #1809) flagged; #5387
  added to #82/#619.
- **#190**: closed #2971/#2633 removed; #5164 added; `parentHamiltonianES_gapped`
  existence flagged for verification.
- **#232**: closed #5407/#2380 flagged; #5434–#5436, #5445, #5449, #5420 and
  splits #5472–#5474 added; #5429/#5444 recorded as closed.
- **#1252**: checklist flipped (24/25 closed); current front and follow-ups
  listed; #128 noted closed.
- **#1373**: closed downstream steps flagged; #2449/#2450 added as the front.
- **#1447**: Jordan-block correction to acceptance criterion 2 recorded.
- **#2147**: cross-references #2661/#2148/#2289 and new #5470 added.
- **#2320**: #2319 closed (residual → #460); #4872/#2660 suggested.
- **#2738**: torus Theorem-3 FT discharged — closeable if scope is
  Theorem-3-only; route issues listed otherwise.
- **#4163**: #4708 added as de-facto precondition.
- **#4164**: tasks linked to #5352–#5357.
- **#4183**: stale working agreements flagged; untracked wave #5347–#5350,
  #5360, #5362, #5363, #5383, #4761, #5045 recorded.
- **#4529**: demolition candidates annotated (4/6 closed); dead
  `SameStateBridgeHyp` reference flagged; #4522/#5437 noted.
- **#4709**: #5135 closed noted; untracked wave recorded; dead #4156 backlog
  pointer flagged.
- **#4866**: #4847 added; queue re-measurement noted.

## 5. Open issues not referenced by any tracker (47 at audit time) — suggested homes

- Wolf coverage: #5422, #5423, #5427, #5428, #5447 → **#3954** (Ch6 tree);
  #5437 → **#20** + **#3954**. New splits #5465–#5469 → **#19**/#3954;
  #5471 → **#995**; #5475/#5476 → **#22**/#3954.
- RFP/MPDO: #5420, #5429, #5434, #5435, #5436, #5444, #5445, #5449, and new
  #5472–#5474 → **#232**.
- PEPS: #2470, #2616, #2707, #2720, #2921 → **#1252**; #2750, #2780, #2781,
  #2787 → **#2738** (or #1252); #4522 → **#4529**.
- 1708.00029: #5387 → **#82** + **#619**.
- SPT/RMP: #2660 → **#2320**; #4872 → **#2320** (+#2147); #1529 → **#1809**;
  new #5470 → **#2147**/#2289.
- tenkz: #4761, #5347, #5348, #5349, #5350, #5360, #5362, #5363, #5383 →
  **#4709** (and/or #4183); #5352–#5357 → **#4164**.
- Lean infra: #4847 → **#4866**; #4037, #4564 (already under #4529), #5045 →
  judgment call (#5045 fits no current tracker; #4183 adjacent).

These homes were recorded in the tracker refresh sections applied 2026-08-04.

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
- This report file briefly disappeared from the worktree on 2026-08-04
  (another agent process was operating in the tree) and was restored from
  the audit session.

## Appendix: full status table (145 issues)

CLOSED by audit (14): #631, #2318, #2470, #2616, #3965, #4065, #5086, #5422,
#5428, #5429, #5444 (completed); #2750, #2781, #4943 (superseded).

| Issue | Status | Note |
|---|---|---|
| #19 | tracker, updated | §4 |
| #20 | tracker, updated | §4 |
| #21 | tracker, updated | §4 |
| #22 | tracker, up-to-date + refresh note | |
| #23 | PARTIAL | stationary-support structure |
| #24 | ACTIVE | depends on #3984 Cesaro package → #5476 |
| #27 | PARTIAL | Thm 6.14 done; Cors 6.6-6.7 Kraus-only |
| #82 | tracker, updated | #5342 closed; #5387 added |
| #125 | ACTIVE | |
| #126 | ACTIVE | |
| #138 | tracker, updated | open tasks were fully closed → #3974/#3975 |
| #139 | ACTIVE, split filed | Thm 6.15 → #5475 |
| #190 | tracker, updated | #5164 added; closed #2971/#2633 dropped |
| #232 | tracker, updated | new follow-ups + splits added |
| #460 | ACTIVE | capstone; sole live leaf is #952/#5164 |
| #619 | tracker, updated | #5342 closed; #5387 added |
| #622 | ACTIVE, redundant with #664 | retitle Tracking: or close |
| #664 | ACTIVE | blueprint path renamed ch11b→ch22 |
| #764 | ACTIVE | |
| #765 | ACTIVE | |
| #766 | ACTIVE, needs reframe | cited declaration deleted (statement false); see `docs/paper-gaps/wolf_prop2_11_lorentz_scalar_filtering_gap.tex` |
| #829 | ACTIVE | |
| #952 | ACTIVE, cross-linked with #5164 | |
| #992 | tracker, updated | Ch1 not closed; #3958 added |
| #995 | tracker, updated | #3972 complete; #5471 added |
| #996 | tracker, up-to-date | |
| #1252 | tracker, updated | checklist flipped 24/25 |
| #1373 | tracker, updated | #2449/#2450 added |
| #1447 | tracker, updated | Jordan-block statement correction |
| #1529 | ACTIVE | link #1809 |
| #1809 | tracker, updated + summary posted | |
| #2147 | tracker, updated | #2661/#2148/#2289/#5470 cross-referenced |
| #2148 | PARTIAL, split filed | SO(3) piece → #5470 |
| #2289 | tracker, up-to-date | |
| #2320 | tracker, updated | |
| #2449 | PARTIAL | |
| #2450 | PARTIAL | |
| #2606 | ACTIVE | |
| #2660 | PARTIAL, cross-linked with #4872 | defs landed PR #2978 |
| #2661 | tracker, up-to-date | |
| #2691 | ACTIVE | |
| #2707 | ACTIVE | |
| #2720 | PARTIAL | |
| #2723 | ACTIVE | |
| #2738 | tracker, updated; closeable candidate | if Theorem-3-only scope |
| #2780 | ACTIVE | |
| #2787 | ACTIVE | owns the live residual |
| #2921 | ACTIVE | |
| #2947 | ACTIVE | link #2320 |
| #3371 | ACTIVE | |
| #3394 | ACTIVE | |
| #3396 | ACTIVE | work in flight |
| #3399 | PARTIAL | |
| #3400 | PARTIAL | infrastructure only |
| #3401 | PARTIAL, split filed | Breuer–Hall indecomposability → #5471 |
| #3402 | PARTIAL | Prop 3.8 reverse directions open |
| #3616 | ACTIVE | open PR #5446 closes it |
| #3622 | PARTIAL | |
| #3623 | PARTIAL | prerequisite 1/3 done |
| #3954 | tracker, updated | dangling refs; line-198 equality criterion untracked |
| #3958 | tracker, up-to-date | |
| #3959 | PARTIAL | small |
| #3960 | ACTIVE | |
| #3961 | PARTIAL | |
| #3962 | ACTIVE | |
| #3963 | ACTIVE, split filed | → #5465/#5466/#5467 |
| #3964 | ACTIVE | |
| #3966 | PARTIAL, split filed | → #5468/#5469 |
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
| #3984 | PARTIAL, split filed | Cesaro package → #5476 |
| #4037 | PARTIAL | nearly done; ~9 residual suppressions |
| #4158 | ACTIVE (standing) | stays open by design |
| #4162 | PARTIAL | core landed 2026-08-02; checkboxes unticked |
| #4163 | tracker, updated | #4708 added |
| #4164 | tracker, updated | #5352–#5357 linked |
| #4183 | tracker, updated | dead backlog pointer; untracked wave recorded |
| #4522 | PARTIAL | link #4529 |
| #4529 | tracker, updated | 4/6 demolition candidates closed |
| #4564 | PARTIAL | 7 waves landed; small residue in `BNTBlockIntersection.lean` |
| #4565 | PARTIAL | Lean route retired; dormant ch23 blueprint files remain |
| #4699 | ACTIVE | |
| #4703 | tracker, up-to-date | |
| #4708 | PARTIAL | |
| #4709 | tracker, updated | untracked wave recorded |
| #4761 | ACTIVE (standing) | 13 live review threads |
| #4847 | PARTIAL | P1/P2/P5/P3-A landed; link #4866 |
| #4866 | tracker, updated | #4847 added |
| #4872 | PARTIAL | Lemma 1 virtual form exists; blueprint not synced |
| #4904 | PARTIAL | 1/5 defects fixed; defect 5 → #5350 |
| #5045 | ACTIVE | unaddressed |
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
| #5406 | PARTIAL, split filed | → #5472/#5473/#5474 |
| #5420 | ACTIVE | link #232 |
| #5423 | ACTIVE | |
| #5427 | ACTIVE | Brouwer available in vendored Gametheory dep |
| #5434 | ACTIVE | |
| #5435 | ACTIVE | |
| #5436 | ACTIVE | |
| #5437 | ACTIVE | link #20/#3954 |
| #5441 | ACTIVE | |
| #5445 | ACTIVE | |
| #5447 | ACTIVE | unital half of #5422's scope |
| #5449 | ACTIVE | |
