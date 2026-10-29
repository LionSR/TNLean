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
no builds; compilation and axiom checks were performed separately by the owner.

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
- Canonical `leanblueprint checkdecls`, web/PDF builds, ChkTeX and the pinned
  `latexindent` check were not run: those tools/artifacts are absent locally.
  No additional tool download was attempted. The required shared
  `lean-conventions` skill was also absent; its GitHub API retrieval returned
  HTTP 403, so the available local convention documents were followed.
  No permission bypass or retry was attempted.

The inverse-gap cutoff removes this specific source-rate obstruction: the
starting-cutoff term `log d * √((t₀+s)/g)` no longer inherits `g⁻³ᐟ²` from
`t₀ ∝ g⁻²`. This file does not prove the final entropy or MPS rate. The
independent rank logarithm, scalar schedules, entropy assembly and sequential
MPS conversion remain with their respective workers. No publication, CI run
or merge is performed by this refinement task.
