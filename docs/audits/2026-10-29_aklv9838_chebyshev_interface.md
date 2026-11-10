# Actual truncated-chain Chebyshev interface

Public branch: `codex/aklv-chebyshev-9838-public`.
Publication base: `b0e62a1ff38cc6c71fa301f94449ad855ebf4c25`; the two Lean
proof modules preserve the locally validated source bytes exactly. The
publication adds only the owned AGSP/rank slice and its documentation.
The prior private branch is `codex/aklv-chebyshev-9838`.
Verified prerequisite: `codex/aklv-robustness-9837-public` at
`20acc2f1bb3c9b3f00a53e58d0e50c413fe2e7e0` (GitHub ref and local checkout).
No dependency pins changed. QICLean remains
`acda92aa70e69b37507e422bceb5414036859fe6`; Mathlib remains
`c55e6e786f49471c72fbddbec5415808896aec1e` with Lean `v4.35.0-rc3`.

The inverse-gap refinement is integrated from published proof commit
`c0a899002be548687673b113f6c2cd309e8a8691`, contained in remote-verified
`codex/aklv-inverse-gap-cutoff-public` at the tested head
`b0e62a1ff38cc6c71fa301f94449ad855ebf4c25` (earlier publication
`420ebf9a4e8f958c692c2072a27adb40006ce821` remains preserved).
The original prerequisite and refinement have identical pins.
`AKLV/InverseGapRobustness.lean` is copied by cherry-pick without editing:
its blob is exactly `aebf867a3338df0d01a697813dc444db556cb4dd`.
The tested head was fetched and compared: the Lean proof and all pins are
unchanged; its later differences concern Blueprint registration, formatting
and the refinement audit. The private minimal patch therefore targets that
tested public prerequisite and contains only the two new AGSP/rank modules.

## Compiled public interfaces

`TNLean.MPS.AreaLaw.AKLV.exists_normalized_chain_chebyshev_agsp_of_inverse_gap_cutoff`
is in `TNLean/MPS/AreaLaw/AKLV/ChebyshevProjector.lean`.
It requires:

- Original bonds `h : Fin (L-1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ`,
  supported on `[i,i+2)`, with `0 ≤ h i ≤ 1`.
- Boundary bonds `a<b`, an integer `w≥1`, and `b.val+1=a.val+2*w`.
- Scalar shifts `x,m,y` for which the **actual** left, middle and right
  shifted sums `leftCutBlock h a x`, `middleCutBlock h a b m`,
  `rightCutBlock h b y` are positive semidefinite.
- A unit vector `Ω`, `0≤e≤6`, `0<g≤1`, and the original normalized Hamiltonian
  `H = sum_i h i - (x+m+y)I` satisfying `HΩ=eΩ` and
  `H-eI ≥ g(I-|Ω><Ω|)`. The positive rank-one gap implies uniqueness.
- A real cutoff `t≥32768/g` and any integer degree `k≥1`.

It derives, for
`Ht = clip_t(leftCutBlock h a x) + middleCutBlock h a b m + h a + h b +
clip_t(rightCutBlock h b y)`, a unit vector `φ`, energy `e'∈[0,e]`, and a
real polynomial `p` of degree exactly `k` with `p(e')=1`, such that:

```text
Ht φ = e' φ
Ht - e'I ≥ (g/2) (I-|φ><φ|)
‖Ht‖ ≤ u = 2t + middleCutBudget a b m = 2t + 2w + |m|
K = p(Ht) is Hermitian
K φ = φ
ψ unit and ψ ⟂ φ  ⇒  Kψ ⟂ φ and ‖Kψ‖² ≤ δ
δ = (2 exp(-2k sqrt((g/2)/(u-e'))))²
operatorSchmidtRank(cutOperator [0,a+w+1) K) ≤ D
D = (q*k)^(17*(w + k/(2*w)))
∃ θ : ℝ, ‖Ω - exp(iθ) φ‖² ≤ exp(-t/16).
```

The same `Ht`, `p` and `K` occur in every conclusion. No new gap, rank,
fixed-vector, complement-invariance or contraction certificate is assumed.
No configuration or positive-local-dimension witness is required by this
existence theorem; the unit vector supplies a configuration internally.

The original `exists_normalized_chain_chebyshev_agsp` and spectral/filter
interfaces retain their names and signatures, including their older
`t≥32768*(e+g)/g²` premise. Current consumers can continue to use them;
the new named variant supplies the weaker inverse-gap cutoff.

`exists_frustrationFree_chain_chebyshev_agsp` requires the same positive
supported unit bonds and even-window geometry, a unit vector `Ω` with
`(sum_i h i)Ω=0`, the original rank-one gap with `0<g≤1`,
`t≥32768/g`, and `k≥1`. No normalization shifts or block positivity
hypotheses are required. It derives `HtΩ=0`, the clipped rank-one gap
`g/2` about **that same Ω**, and the filter/rank certificates above with
`e'=0`, `m=0`, `u=2t+2w`. Positive bonds and zero total ground energy
give the frustration-free qualification.

## Reusable supporting results

- `exists_chebyshev_ground_filter`: any finite Hermitian `H`, unit eigenvector
  at `e`, positive rank-one gap `g`, operator ceiling `u`, and `e+g≤u` give
  the degree-`k` spectral filter for every `k≥0`.
- `normalized_chain_real_polynomial_rank`: every real polynomial of degree
  at most `k≥1` in the actual clipped chain has the same cut-rank bound.
  Requires only original supports, even-window geometry, and a value of
  `Fin q` for fixing spectator sites; no spectral, positivity or cutoff
  hypothesis is used.
- `operatorSchmidtRank_aeval_single_window_le_pow` in
  `AKLV/SingleWindowPolynomialRank.lean`: the corresponding complex-polynomial
  result for arbitrary supported exterior matrices and `2*w` actual local
  middle bonds. The private padding adds `2*w+1` zero-interaction sites,
  applies the existing two-window polynomial estimate, and fixes spectator
  configurations. Spectral claims are never made on the padded chain.
- `operatorSchmidtRank_le_embedOp`: the general restriction inequality.
- `operatorSchmidtRank_sheetSplit_eq_cutOperator`: the exact coordinate
  equality needed by the QICLean regional entropy consumer.
- `normalized_chain_truncation_bounds` and `middleCutBudget_eq`: positivity,
  operator ceiling, norm and exact local-bond count.

## Verification and remaining source target

Both owned modules pass targeted Lake builds and strict Lean elaboration
with warnings treated as errors. All thirteen audited public theorems use
only `propext`, `Classical.choice` and `Quot.sound`. An independent native
semantic reviewer passed the completed spectral, physical rank, padding,
real-polynomial, unique-ground-state and frustration-free arguments.
The generated AKLV import aggregate builds. Blueprint synchronization and
reverse coverage pass, all fourteen new blueprint tags resolve by direct
Lean checking, and the eleven-page focused PDF compiles; its new
projector section was visually checked. References to the chain definition
and imaginary-time theorem outside the focused excerpt remain unresolved. Reader-facing prose, generated imports,
whitespace and proof-hazard checks pass. Publication-checkout strict Lean,
axiom audits, direct declaration checks and Blueprint synchronization pass;
the two changed Blueprint files pass pinned latexindent 3.24.7 formatting. The local tactic-pattern scan
recorded the endpoint arithmetic in the ledger; the inherited boundary-norm
pattern is recorded there with its accepted-proof preservation constraint.

The canonical repository-wide `leanblueprint checkdecls` was attempted but
cannot import the unbuilt root `TNLean.olean` in this targeted environment.
Its exact failure is `object file .../TNLean.olean of module TNLean does not
exist`. This is a remaining whole-library validation step for parent CI;
the new module and every new referenced declaration have been checked.

The explicit rank above retains the corrected ordered-gap count from
the existing two-window result. It is `O(s+k/s)` in the exponent for
`s=2w`, sufficient near `k≈s²`; the source's further large-window
optimization `O(max{k/s,√k})` is not proved here.
The older binomial rank bound quoted in the printed Theorem 4.3 is not
substituted for the stated Lemma 4.2.

No favorable `D*δ≤1/2` parameter choice is claimed. The available rank
estimate retains `log(q*k)`: its direct schedule involves `log(q/g)`.
The source's stated uniform pure `log³(q)/g` bound needs a separate
justification of that optimization. The original-Hamiltonian normalization,
all-cut geometry/short-chain cases, truncation-sequence induction and MPS
conversion remain with their respective workers. The inverse-gap cutoff
is now derived from the exact published refinement, while the separate
rank logarithm and favorable-parameter questions remain open.

The unsquared filter is not asserted positive. Squaring the operator would
change its degree and rank, independently of squaring its norm bound.
The norm shrinking used here is exactly the squared parameter expected by
`Entropy.regionEntropy_le_four_log_of_cutOperatorSchmidtRank`.
