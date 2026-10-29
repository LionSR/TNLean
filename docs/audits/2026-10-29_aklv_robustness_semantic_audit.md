# Independent audit of normalized AKLV robustness

## Verdict and scope

A separate native reviewer, `aklv_semantic_audit`, independently reviewed
implementation head `ab882fe038e4559156b73a1f3d8795c2f3279066` against
[AKLV, arXiv:1301.1162v1, Sections 6.1 and 6.3](https://arxiv.org/html/1301.1162v1).
The verdict is **PASS for the requested normalized-chain theorem**. No Lean
proof defect was found. The reviewer found one additional source normalization
typo, recorded below and added to the paper-gap note in this audit commit.

The reviewer read all eleven AKLV modules and the critical existing
commutator/Hadamard, clipping, minimizing-eigenvector, operator-gap and phase
helpers. It did not edit files or run builds concurrently with the owner.
The owner separately repeated compilation and transitive axiom checks.

## Exact statement and source correspondence

The physical entry is `TNLean.MPS.AreaLaw.AKLV.normalized_chain_robustness`
in `TNLean/MPS/AreaLaw/AKLV/NormalizedChain.lean`. Its input consists of:

- original nearest-neighbour supports and positive contractions `0 ≤ hᵢ ≤ I`;
- two boundary bonds `a < b`, three real scalar shifts, and positivity of
  the resulting three regional sums;
- a unit original eigenvector with energy `0 ≤ e ≤ 6` and the original
  operator inequality `H − eI ≥ g(I − |Ω⟩⟨Ω|)`, where `0 < g ≤ 1`;
- cutoff `t ≥ 32768(e+g)/g²`.

There is no assumed commutation, commutator bound, spectral tail, residual,
clipped gap or closeness conclusion. The regional commutations and the sum
identity are derived from the actual supports and cuts.

| Implementation | Source normalized operator |
| --- | --- |
| `h a`, `h b` | `H₂`, `Hₛ₋₁` |
| `X = leftCutBlock` | `H_L + H₁` |
| `N = middleCutBlock` | `H₃ + ⋯ + Hₛ₋₂` |
| `Y = rightCutBlock` | `Hₛ + H_R` |
| `A = h a + h b` | the two boundary couplings |
| `B = X + N + Y` | `H − A` |
| `K = clip_t X + N + A + clip_t Y` | `H^(t)` |

QICLean's actual `energyTruncation` is spectral clipping by `λ ↦ min(λ,t)`.
The implementation clips the two exterior sums separately. The strict low
projection `P_t = 1 − spectralProjectionGE B t` matches Section 6.3; equality
at the cutoff makes no difference to the clipping function.

The conclusion constructs an actual unit eigenvector `φ` with ground energy
`0 ≤ e′ ≤ e`, proves
`K − e′I ≥ (g/2)(I − |φ⟩⟨φ|)`, and gives a real phase `θ` with
`‖Ω − exp(iθ)φ‖² ≤ exp(−t/16)`. Positivity and this operator inequality
identify the constructed eigenvector as the unique ground line.

The reviewed constants are:

- off-diagonal boundary norm at most `2 exp(−(t−u)/8)`;
- original eigenvector tail at most `2 exp(−(t−20)/8)` for a unit vector;
- gap cutoff `1024(e+g)/g²` and gap at least `g/2`;
- projected residual at most `10 exp(−(t−40)/16)`;
- intermediate squared-distance bound `968g⁻² exp(−(t−40)/8)`;
- full cutoff `32768(e+g)/g²`, absorbing the prefactor to `exp(−t/16)`.

The Blueprint statements match these signatures and constants. The corrected
cross-term estimate bounds the unsquared modulus by `2√(E_K/t)`.

## Additional source finding and correction

The displayed normalization in v1 Section 6.1 subtracts `d/(s−7)` from
each term with `4 ≤ i ≤ s−3`. That range has `s−6` terms. For `s ≥ 8`
and positive interior ground energy `d`, the printed formula gives ground
energy `d − (s−6)d/(s−7) = −d/(s−7)`, rather than zero. The intended
uniform denominator is `s−6`; equivalently, subtract `dI` from the sum once.
This is an arithmetic inference from the displayed range, independently
verified by the owner after the reviewer reported it.

The intended scalar-shift map is `x=c`, middle shift `m=d`, and `y=c′`.
The added section in `docs/paper-gaps/aklv13_robustness_constants.tex`
records the typo and its correction. The Lean proof does not depend on
the printed distribution of shifts. It accepts the resulting regional
positivity and energy bound directly, as appropriate to its normalized scope.

## Verification and limits

Fresh owner verification after the independent review:

- Pinned Lean `v4.35.0-rc3`, Mathlib
  `c55e6e786f49471c72fbddbec5415808896aec1e`, and QICLean
  `acda92aa70e69b37507e422bceb5414036859fe6` retained.
- `lake exe cache get` found no files to download and 8943 already
  decompressed artifacts; `Mathlib.olean` was checked before building.
- `lake build TNLean.MPS.AreaLaw.AKLV` passed, reporting 3260 jobs.
- All eleven modules passed strict direct elaboration with warnings as
  errors, `relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`, and the
  standard Mathlib linter set.
- A fresh `#print axioms` audit of all 44 public declarations found only
  `propext`, `Classical.choice`, and `Quot.sound`. This checks transitive
  dependency closure, including private helpers. Temporary audit source was
  removed; no new axioms or proof bypasses were introduced.
- Generated import consistency, changed-declaration Blueprint coverage,
  forbidden-token checks and whitespace checks passed.
- The pinned deterministic LaTeX formatter passed for both changed Blueprint
  files after a whitespace-only alignment correction. ChkTeX is unavailable.
- The amended paper-gap note rendered using a temporary standalone wrapper
  omitting the unavailable shared preamble; this is a limited TeX check.

The implementation is additive relative to its base; existing ALVV viability
files and existing public theorem signatures are unchanged. Construction of
the normalization from arbitrary unshifted input is outside this normalized
theorem. A full-root regression build and canonical Blueprint declaration,
web and PDF builds were not run locally. The `leanblueprint` CLI and the
shared preamble's `dsfont.sty` are unavailable in this environment.
Hosted CI status is reported separately with the draft PR.
