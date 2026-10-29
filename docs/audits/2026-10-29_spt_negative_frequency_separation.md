# Negative-frequency separation of actual ground correlations

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3, equations
(3.1)–(3.6), https://arxiv.org/pdf/math-ph/0507008. This is an auxiliary
spectral step for #9879 and the SPC11 Section II.F physical-path converse.

The symmetric Gaussian low-pass filter in #10305 does not isolate the
ordinary connected correlation. The new operation retains exactly the
energy-lowering matrix elements in the actual Hermitian energy basis,
using Mathlib's canonical rank-one operators. The full actual ground
projection is removed. Annihilation of ground vectors and equality with
the actual commutator are proved by spectral expansion, not assumed.

For a one-dimensional ground eigenspace the projection formula gives the
ordinary connected correlation with its original, unnormalized ground
vector. The denominator is its squared norm. The physical-path caller
uses the actual ring Hamiltonian and periodic MPS vector; its least-energy
ordering and full ground line are derived from the physical-path data.
No transfer spectral condition, correlation estimate or continuous minimal
gauge is added as a hypothesis.

The generic algebraic statement allows degenerate exactly equal ground
energies. It does not identify a quasi-degenerate finite-volume ground
band with a single exact eigenspace. The physical-path application has
an exact unique ground line, as stated in that path predicate.

Remaining: regularize the sharp frequency selector with the source
Gaussian/Cauchy time kernel, prove the corresponding approximation error,
bound the regularized commutator using finite-ring Lieb–Robinson, and pass
the actual correlations to limiting transfer contractions/minimal gauges.
The sharp operator is not claimed local. No full exponential clustering
or SPT converse is asserted by this draft.

No local Lean command, build, elaboration or checkdecls was run, as
requested. New Blueprint entries remain notready pending hosted proof
acceptance. Source/import/prose/formatting/integrity checks and independent
mathematical review do not replace Lean verification.

The same draft now constructs the actual scalar Gaussian selector as the
right tail of the centered Gaussian of variance Δ²/q. Mathlib's exact
Gaussian moment-generating function supplies its sub-Gaussian parameter;
Chernoff at ±Δ gives the explicit e^(-q/2) errors on both gap regions.
These are derived probability bounds, with no tail-error premise. They
match the scalar Gaussian in Hastings–Koma Lemma 3.1, equation (3.7), for
α=Δ²/(2q). The Cauchy time-integral representation and its operator-locality
application remain unproved by this slice.

The actual Gaussian/Cauchy time kernel is also constructed. Its rational
factor has the convergent half-line Laplace representation from the exact
complex exponential integral. Positive regularizer ε bounds its norm by
(2πε)^(-1)exp(-αt²); every frequency-modulated kernel is absolutely
integrable and its integral norm is bounded by (2πε)^(-1)sqrt(π/α).
The ε dependence is explicit. The double-integral interchange and zero-ε
limit identifying this kernel with the actual Gaussian selector remain
open; a finite bound growing as ε^(-1) does not discharge that limit.
