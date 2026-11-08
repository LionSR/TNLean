# AKLV robustness with an inverse-gap cutoff

The new normalized-chain theorem proves the same ground-vector and gap
conclusions as the accepted robustness theorem at **t ≥ 32768/g**, improving
its cutoff **32768(e+g)/g²**. The operator being clipped is unchanged.

Base: `20acc2f1bb3c9b3f00a53e58d0e50c413fe2e7e0` on
`codex/aklv-robustness-9837-public`, verified against
[PR #10327](https://github.com/LionSR/TNLean/pull/10327).
The refinement is isolated in `TNLean/MPS/AreaLaw/AKLV/InverseGapRobustness.lean`.
All eleven accepted AKLV proof modules are byte-identical to that base.
The existing Blueprint chapter is extended by an appended section; its original
prefix, including the accepted theorem and proof, is byte-identical.

## Source and normalization audit

Primary source: [AKLV, arXiv:1301.1162v1, Sections 6.1–6.3](https://arxiv.org/html/1301.1162v1),
Theorem 6.1 (`thm:Ht`, source lines 949–963), Lemmas 6.4–6.8
(`l:mark`, `l:1`, `l:combounds`, `l:smalltail`, proof lines 1079–1491).
The available primary HTML was inspected for all corresponding statements and
proofs; the TeX file with those original line numbers is absent locally.

Here `e` is the ground energy **after regional scalar shifts**, and `g` is the
original spectral gap, unchanged by those shifts. Section 6.1 supplies
`0 ≤ e ≤ 6` and `0 < g ≤ 1`. It does not establish `e = 0`.
Subtracting `eI` from a regional block can destroy its positivity; inserting
such a shift inside an exterior clipping changes the clipping operator.
Thus substituting `e=0` in the accepted theorem would not justify a refinement.
The displayed source cutoff really is of order `(e+g)/g²`; Section 6.2's use
of a constant starting cutoff does not establish uniform dependence on `g`.

The actual operators throughout the refinement are

- `L = leftCutBlock h a x`, `N = middleCutBlock h a b m`,
  `R = rightCutBlock h b y`, all positive and pairwise commuting;
- `A = h a + h b`, with `0 ≤ A ≤ 2I`;
- `H = L+N+R+A = ∑ i, h i − (x+m+y)I`;
- `K = clip_t(L)+N+A+clip_t(R)`, with `clip_t` the scalar function `min(·,t)`;
- `Q = 1_[t,∞)(L+N+R)` and `P = I−Q`.

Constructing the regional shifts and `e ≤ 6` from arbitrary raw-chain input
is outside this refinement and remains with the normalization worker.

## Why the stronger comparison works

For `x ⟂ Ω`, write `u=Px`, `v=Qx`. The original gap, unit norm of `Ω`,
and `⟨Ω,u⟩=−⟨Ω,v⟩` give

`⟨u,Ku⟩ = ⟨u,Hu⟩ ≥ (e+g)‖u‖²−g‖v‖²`.

The existing high-mass theorem applied to `v`, using `Qv=v`, gives
`⟨v,Kv⟩ ≥ t‖v‖²`. The cross-block identity and `‖A‖≤2` give
`|⟨u,Kv⟩| = |⟨u,Av⟩| ≤ 2‖u‖‖v‖`. Consequently

`⟨x,Kx⟩ ≥ (e+g)‖u‖²+(t−g)‖v‖²−4‖u‖‖v‖`.

Completing the square, `(g‖u‖−4‖v‖)² ≥ 0`, yields
`4‖u‖‖v‖ ≤ (g/2)‖u‖²+(8/g)‖v‖²`. Therefore
`t ≥ e+3g/2+8/g` implies `⟨x,Kx⟩ ≥ (e+g/2)‖x‖²`.
The accepted proof instead discards the positive high diagonal, then bounds the
cross term through `√(E_K/t)`. That loss produces its quadratic inverse gap.
No new locality or physical assumption is needed to retain the diagonal.

Under `e≤6`, `0<g≤1`, the condition `tg≥16` suffices for this gap comparison.
The existing residual and phase estimates need only `tg≥32768` to absorb
`968g⁻² exp(−(t−40)/8)` into `exp(−t/16)`. This proves the new full cutoff.

## Exact compiled declarations

All names have prefix `TNLean.MPS.AreaLaw.AKLV`.

| Declaration | Inputs specific to the estimate | Conclusion |
| --- | --- | --- |
| `orthogonal_clipped_energy_ge_of_inverse_gap_cutoff` | Commuting PSD `L,N,R`, `0≤A≤2I`, unit `Ω`, original quadratic gap, `g>0`, `t≥0`, `t≥e+3g/2+8/g` | Clipped energy ≥ `(e+g/2)‖x‖²` for `x⊥Ω` |
| `exists_ground_gap_twoSidedEnergyTruncation_of_inverse_gap_cutoff` | Same, plus `HΩ=eΩ` | Actual unit minimizing eigenvector `φ`, `0≤e′≤e`, absolute excited-energy threshold `e+g/2`, operator gap ≥ `g/2` |
| `exists_robust_ground_twoSidedEnergyTruncation_of_inverse_gap_cutoff` | Original nearest-neighbour supported positive contractions; commuting PSD regional blocks whose sum is an original bond subsum minus a real scalar; original unit eigenvector and quadratic gap; `0≤e≤6`, `0<g≤1`, `t≥32768/g` | Actual ground eigenvector, quadratic operator gap `g/2`, and a real phase with squared distance ≤ `exp(−t/16)` |
| `normalized_chain_robustness_of_inverse_gap_cutoff` | Original nearest-neighbour supported positive contractions; removed bonds `a<b`; three real shifts making the actual regional sums PSD; original unit eigenvector and matrix PSD gap; `0≤e≤6`, `0<g≤1`, `t≥32768/g` | Same, with the gap stated directly as a matrix PSD inequality |

The first two declarations require neither `e≤6` nor `g≤1`. The last two
require both; the bounds enter the normalized cutoff and locality tail.
The physical entry derives the regional commutations and reconstruction from
original supports. No tail, residual, clipped gap, ground-vector closeness,
or rank/entropy conclusion is assumed.

## Independent native semantic review

The separate native reviewer `/root/semantic_review` reviewed the proposed
estimate, then read all four actual signatures/proofs and the appended
Blueprint section. Final verdict: **PASS**. The reviewer checked the retained
high diagonal, cross absorption, min–max construction, residual argument and
physical reconstruction. It found no circularity, hidden improved-gap
hypothesis or unjustified zero-energy normalization. It made no edits and ran
no builds; compilation and `#print axioms` audits were performed separately by the owner.

## Verification and remaining limits

- Exact Lean `v4.35.0-rc3`, Mathlib
  `c55e6e786f49471c72fbddbec5415808896aec1e`, and QICLean
  `acda92aa70e69b37507e422bceb5414036859fe6` pins retained.
- Existing dependency checkouts and cached `Mathlib.olean` verified before
  building. An independent cache copy was used, with cross-commit TNLean
  outputs removed. No Mathlib source rebuild or pin change.
- `lake build TNLean.MPS.AreaLaw.AKLV.NormalizedChain` passed (3259 jobs),
  then the new target passed (3260 jobs; changed module 8.9 seconds).
  The AKLV aggregator target also passed (3261 jobs).
- Strict elaboration passed with warnings as errors, strict implicits,
  `maxSynthPendingDepth=3`, and the standard Mathlib linter set.
- Exact `#check` and transitive `#print axioms` for all four public declarations
  passed: only `propext`, `Classical.choice`, `Quot.sound`. Temporary Lean
  audit source was removed.
- Six temporary endpoint/regression calculations passed: maximal normalized
  energy and gap, zero energy, gaps `1/2` and `1/1024`, and strict improvement
  over the accepted cutoff at those two smaller gaps. No test fixtures added.

- Import generation/check, Blueprint source-declaration synchronization and
  reverse coverage, forbidden-token, changed reader-facing prose, module-size,
  and whitespace checks passed. The targeted tactic scan's repeated boundary
  norm proof is recorded in the ledger; cross-file extraction is deferred by
  the explicit requirement to preserve accepted proof bytes.
- The appended Blueprint section compiled as a one-page standalone PDF using
  a temporary minimal preamble. This does not establish canonical Blueprint
  rendering or cross-reference resolution.
- At initial validation, canonical `leanblueprint checkdecls`, web/PDF builds,
  ChkTeX and the pinned `latexindent` check were not run: the required
  tools/artifacts were absent locally.
  No additional tool download was attempted. The required shared
  `lean-conventions` skill was also absent; its GitHub API retrieval returned
  HTTP 403, so the available local convention documents were followed.
  No permission bypass or retry was attempted.

The inverse-gap cutoff removes this specific source-rate obstruction: the
starting-cutoff term `log d * √((t₀+s)/g)` no longer inherits `g⁻³ᐟ²` from
`t₀ ∝ g⁻²`. This file does not prove the final entropy or MPS rate. The
independent rank logarithm, scalar schedules, entropy assembly and sequential
MPS conversion remain with their respective workers. Initial delivery was local; subsequent publication and integration are
recorded below. No repository merge or review approval is performed by the owner.

## Integration with the current prerequisite

The published refinement head `420ebf9a4e8f958c692c2072a27adb40006ce821`
and original local commits are preserved. The prerequisite was freshly fetched
at `9279b8ecb1b9f2a6495de699c1c285dd3b6595ec`; its delta from the original
base changes only the paper-gap source-key registry and the note's verdict
marker. These accepted changes were merged without rewriting either history.
The stacked diff against that prerequisite contains only the original five
refinement paths and does not revert either prerequisite change.

The Lean proofs and all accepted AKLV modules are unchanged. The pinned
`latexindent 3.24.7` formatter adjusted two alignment lines in the new
Blueprint section; its deterministic temporary-copy check passed, and the
accepted chapter prefix remains byte-identical. The explicitly requested
Blueprint tools were installed in a temporary virtual environment; no project
pin was changed. `texra-blueprint v0.3.8 paper-gaps check` passed with 275
resolved referenced slugs and registered source keys.

After integration, `lake build TNLean.MPS.AreaLaw.AKLV` passed (3261 jobs),
and strict warnings-as-errors elaboration passed again. All four declarations
were checked through the public AKLV aggregator, and their transitive dependency
closures again contain only `propext`, `Classical.choice`, and `Quot.sound`.
Canonical `leanblueprint checkdecls` was attempted: its executable built, then
failed because the unbuilt repository-wide `TNLean.olean` is absent. This is
not a canonical declaration-check pass. The targeted declaration/export checks
passed; full-root declaration, web/PDF and ChkTeX gates remain for hosted CI.

## Integration onto main after the prerequisite merge

PR #10327, which addresses the normalized robustness obligation in #9837,
was squash-merged into main at
`6da5dd6c42ae8a911097290fac25b673286cd1ae`. That main head and both public
branches were freshly fetched. The existing refinement head
`b0e62a1ff38cc6c71fa301f94449ad855ebf4c25` is preserved as a parent while
main is merged normally; no force push or history rewrite is used.

The squash caused two add/add conflicts: the generated AKLV aggregator and
its Blueprint section. They were resolved by keeping the exact accepted main
content and appending the existing refinement. All eleven accepted AKLV proof
modules remain byte-identical to main. The new proof module remains
byte-identical to its independently reviewed and previously green public head.
The accepted Blueprint section is still an exact prefix of the extended file.
No prerequisite, unrelated main change, dependency pin or source result is
reverted.

Main introduced `blueprint/roles.json` after the original branch point. Its
registry did not yet contain the three newly merged AKLV headline results.
The integration registers those three existing labels and the stronger
inverse-gap robustness theorem, with mathematical-role notes, under the
one-dimensional preliminaries chapter. This preserves the accepted theorem
environments and proof text. Thus the main-target refinement is six paths:
the original five plus this required role registry entry. The global role
check passes.

A separate native integration reviewer independently checked the exact
six-path working-tree diff against `6da5dd6c`, all eleven accepted proof files,
the unchanged new proof file, the exact accepted Blueprint prefix and the
four role registrations. Verdict: **PASS**. No mathematical hypotheses or
conclusions changed; the reviewer made no edits and ran no builds.

After integrating main, the pinned AKLV target build passed again (3261 jobs)
and the new proof module passed strict warnings-as-errors elaboration with
strict implicits and standard Mathlib linters. All four declarations were
checked through the public aggregator; their transitive dependency closures
again contain only `propext`, `Classical.choice`, `Quot.sound`. Maximal-energy
and small-gap endpoint calculations passed. The temporary Lean source was
removed. Exact root dependency pins and the existing Mathlib cache were
verified before these checks; no Mathlib source build or pin change occurred.

Pinned formatting and the global mathematical-role check passed; all eight
role-tool unit tests passed. Import generation, Blueprint source/declaration
synchronization and reverse coverage, forbidden-token, reader-facing prose,
numbered-file and whitespace checks passed. The pinned paper-gap checker
resolved all 276 referenced slugs on current main.

The existing PR #10331 is being retargeted to main. Its earlier stacked-head
CI run 40894754380 passed all applicable jobs, including full Lean/strict/timing
checks, Blueprint web validation, ChkTeX, deterministic formatting, the main
PDF and the FT-MPS volume. That earlier success is not claimed for the new
main-integration head: its exact-head CI must run separately. The PR remains
a bounded improvement to the accepted #9837 robustness result, supporting
#9838–#9840; raw-chain normalization and the whole area-law/MPS conclusions
remain outside this refinement. The parent coordinates readiness and merger.

## Reconciliation with subsequent main changes

The existing PR was rechecked at public head
`365e8d5063c1a5b29c77a5aeea32d05ce2c471ea`: no other author had changed its
branch, no local build process was running, and no review comments or review
requests were outstanding. Current main was freshly fetched at
`7137c7c7452f91c21ebdd7283536fe09939fd62f`. Root dependency pins and the
accepted AKLV proof modules were unchanged.

The merge produced one conflict, between appended tactic-ledger entries.
Every current-main entry was preserved. The refinement's same two entries,
25 lines in total, now appear once under the ledger's existing Candidates
section. Removing precisely those added lines returns the exact main ledger;
this avoids competing with unrelated end-of-file appends. No other author's
content was removed or rewritten.

The resulting main-relative diff remains six scoped paths. The inverse-gap
proof and its four signatures are byte-identical to the previously reviewed
public head; all eleven accepted proof modules match main. Main's accepted
Blueprint content remains an exact prefix, and the role-registry merge
preserves main's newer Hastings labels while retaining the same four AKLV
registrations. A separate native reviewer checked the final integration diff
and ledger relocation: **PASS**, with no proof/statement change, prerequisite
reversion or overlap with the separate original-chain normalization bridge
#10371. The reviewer made no edits, ran no builds and took no remote actions.

Fresh verification after reconciliation passed: the pinned AKLV build
(3261 jobs), strict warnings-as-errors elaboration, four public exports with
only `propext`, `Classical.choice`, `Quot.sound` in their transitive dependency
closures, maximal-energy and small-gap endpoint checks, import generation,
global role checks and all eight role-tool tests, pinned formatting, Blueprint
synchronization and reverse declaration coverage. The pinned paper-gap
checker resolved all 279 current-main slugs. No Mathlib or dependency source
rebuild, pin upgrade, new mathematical assumption or proof bypass was used.

Before publication of this reconciliation, the old-head CI run 40919572908
had passed the Lean build/strict/timing gates, module policy, inline diagrams
and PDF checks; its web-page validation was still running. That status is
kept distinct from validation of the reconciled head, which requires its own
exact-head CI. Readiness and merge transitions remain centrally coordinated.
This PR continues to refine the normalized #9837 robustness theorem only;
it does not duplicate #10371 or claim the whole area-law/MPS obligations.
