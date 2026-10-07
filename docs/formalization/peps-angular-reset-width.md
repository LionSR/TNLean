# Uniform angular-reset width

This package addresses the uniform numerical scale estimate in issue #8766.
It does not establish the physical information-reset lemma or the angular
information proposition.

## Source and scope

The source is the September 24, 2026 polynomial-PEPS manuscript at
`openai/math` revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex`,
lines 744–778, equation `eq:info-reset-scale-cost` and its following argument.
The source text was fetched at that immutable revision and compared exactly;
its SHA256 is `b88596a7f6f4f0e6b49a030f27ca9ca64aa669941d8393070fddfe49b08e9cab`.
The Lean proof text is original. No upstream Lean implementation is copied.

For fixed real coefficients and exponent, the polylogarithmic contribution
is sublinear in the scale. With a positive slope `c`, choose a positive `D`
satisfying `4 * C4 / c ≤ D`. One size threshold then works simultaneously
for every sufficiently large `L` and every `s ≥ D * log L`.
The sum of the two width contributions is at most `3 * c * s / 4`, hence
strictly smaller than `c * s`.

The choice of `D` precedes the size threshold; both precede `L` and `s`. Their allowed dependence on
physical parameters is inherited from the fixed coefficients and exponent. In particular `D = max 1 (4 * C4 / c)` remains positive
when the logarithmic coefficient vanishes. The real exponent is fixed but
not bounded by a universal constant.

The proof uses Mathlib logarithmic asymptotics to obtain an eventual bound
at every larger scale. Thus it does not need the derivative-based
monotonicity argument used in the manuscript. It proves the same uniform
inequality without postulating an eventual estimate.

## Remaining dependencies

The physical reset theorem, the derivation of its width upper bound,
geometric core clearance, entropy-continuity estimates, and annular
induction remain separate obligations. Existing localization, encoded-frame,
and ownership work is not changed. No dependency pin update is required.
