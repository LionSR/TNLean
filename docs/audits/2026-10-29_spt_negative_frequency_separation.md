# Actual negative-frequency separation and Gaussian/Cauchy scalar limit

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3, equations
(3.1)–(3.14), https://arxiv.org/pdf/math-ph/0507008. These are supporting
spectral and analytic steps for #9879 and SPC11 Section II.F.

The actual sharp negative-frequency part is the sum of the energy-lowering
matrix elements, written with Mathlib's canonical rank-one operators.
It annihilates ground vectors. Its actual ground commutator equals the
correlation with the entire ground projection removed. In a one-dimensional
ground space, the projection formula gives the ordinary connected
correlation of the original unnormalized vector, with its squared norm
explicit in the denominator. The exact MPS-path caller derives least-energy
ordering and the complete ground line from the actual physical path.

The actual Gaussian selector is the right tail of the centered Gaussian
of variance Δ²/q. Reuse QICLean's exact Gaussian sub-Gaussian-MGF theorem
and Mathlib's Chernoff bound: both gap regions have explicit e^(-q/2)
error. No tail, spectral-filter or approximation premise is assumed.

The actual Gaussian/Cauchy time kernel has a convergent half-line Laplace
representation. For a fixed positive regularizer ε, it is absolutely
integrable and admits the explicit finite bound
(2πε)^(-1)sqrt(π/α). Its ε dependence is retained.

The stronger transform identity is derived using the normalized Gaussian
time measure. In the product with positive half-line volume, the actual
joint Laplace/phase integrand has norm exp(-εs), hence is absolutely
integrable. Fubini and QICLean's exact Gaussian characteristic function
identify the actual transform with the damped half-line Gaussian integral.
A translated Gaussian majorant, independent of ε>0, permits the zero-ε
limit. The Gaussian density and translated indicator integral normalize
this limit to the actual inverse-variance Gaussian tail. Thus the scalar
Cauchy/Gaussian identity is proved rather than made an assumption.

The exact algebraic ground-space statement permits degeneracy at a single
energy. It does not replace a quasi-degenerate finite-volume ground band
by one exact eigenspace. The physical-path caller has an exact unique
full ground line, as its predicate states.

Remaining: construct the actual regularized observable, relate its matrix
elements to this scalar transform, control its ground commutator uniformly
by finite-ring Lieb–Robinson, and derive ordinary exponential clustering.
Passing finite correlations to limiting transfer contractions and minimal
gauges is also separate. No locality of the sharp spectral part and no
full clustering/SPT converse are asserted here.

No local Lean command, build, elaboration or checkdecls was run, as
requested. Blueprint entries remain notready pending hosted acceptance.
Independent source/API reviews found no concrete mathematical mismatch.
First hosted diagnostics exposed elementary name, set-membership and
coercion-normalization issues in the foundations; these are source-repaired.
Native source/import/prose/format/integrity checks do not replace Lean
verification of the new scalar-limit assembly.
