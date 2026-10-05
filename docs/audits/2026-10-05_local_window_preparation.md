# Physical preparation from local windows

This result strengthens the quantitative preparation development associated with
[arXiv:2307.01696](https://arxiv.org/abs/2307.01696). It does not identify the
paper's qualitative finite-correlation definition with a quantitative local
minorization condition.

## Mathematical content

For fixed square bond dimension `D`, window width `s > 0`, and strength `η > 0`,
assume actual site transfer maps are trace preserving and every available
nonwrapping `s`-window has normalized output-first Choi matrix at least
`(η / D) • (τ ⊗ I)` for some density matrix `τ`. Minorizers can vary with the
window and ring, and can be singular.

The proof constructs compatible cyclic density references from a whole-ring
fixed density. It derives the interval Gram bound
`2 D (1 - η) ^ (n / s)` and a uniform transfer-matrix bound. A final remainder
uses complete positivity and trace preservation without requiring a short-window
minorizer. The `η ≤ 1` fact is derived from the genuine `N = s` window; weakening
to `η / 2` handles `η = 1` before taking a positive logarithmic rate.

The resulting preparation theorem supplies a uniform cutoff at least `s` and
physical depth `C log(N / ε)` for the original family. Global mixing, compatible
references, common stationarity, faithfulness and short-ring nonvanishing are not
input assumptions. The cutoff is necessary: the regression includes a zero
one-site periodic vector and no available two-site window.

## Reuse and architecture

- `MPS/Chain/Interval` defines actual intervals and their ordered products.
- `InhomogeneousChoiResidual` factors the existing Choi/Gram argument into a
  shared residual product bound, including nonuniform strengths.
- `WindowMixing` constructs cyclic references and assembles complete windows
  plus a trace-preserving remainder.
- `WindowMixingPreparation` consumes the existing varying-reference theorem.
- The old common-faithful preparation statements and sharper exponent remain
  unchanged. Their proofs reuse the same residual and reshuffling facts.
- Rectangular bonds remain separate: zero-padding does not preserve full-space
  trace preservation.

## Validation boundary

The complete new proof bodies and regression declarations passed a strict
scope-isolated check using already compiled prerequisites, with warnings treated
as errors. This is provisional exact-body validation, not a complete production
import-graph build. The guarded capstone kernel-dependency check contains only `propext`,
`Classical.choice`, and `Quot.sound`. The subsequent full repository check
is recorded below.

The concrete alternating Pauli-X/rank-one-reset regression covers distinct
singular minorizers, maximal strength, a nonempty remainder, a zero short ring,
and the original-family preparation consumer. It is wired into strict CI.

The extended nine-panel diagram regression checks all prior ordered-mixing
panels and the two-window reference-transport equation. Its open index is a
Liouville matrix-entry index; the first window acts outermost. Both panels have
the same typed boundary. The diagram was rendered and visually inspected.

## Full repository validation checkpoint

The complete production-import Lean build and compiled blueprint checks passed
on remote head `8717875dcd9636007e63f6f67b3128baa0e0ad06` in
[PR CI run 37294651873](https://github.com/LionSR/TNLean/actions/runs/37294651873).
This discharges the original full-build condition described above for that
snapshot. The subsequent main integration and review documentation corrections
require their own exact-head CI; their result is recorded in the pull request.
