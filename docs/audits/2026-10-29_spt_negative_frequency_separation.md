# Ordinary connected clustering from the actual physical MPS gap

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

The actual regularized observable is now constructed as the Gaussian
Bochner integral of the Cauchy-weighted actual dynamics. Its inverse-ε
norm bound proves integrability. A matrix-element functional made from
existing bilinear maps transports the integral to the actual scalar
transform, so the energy entries have the proved Gaussian-tail limit.

Uniform locality uses a different bound. At nonzero time the Cauchy factor
has norm at most 1/|t|. The actual Lieb–Robinson increment cancels that
factor at short times using exp(x)-1≤x exp(x); at zero the actual
commutator vanishes. At long times use 1/T and the norm bound
2‖A‖‖B‖. Splitting the actual Gaussian integral gives a bound independent
of ε>0. The actual finite-ring caller supplies the propagation estimate
from its local Hamiltonian, without an extra locality/correlation premise.

The actual regularized ground vectors and adjoint ground vectors have
limits obtained from their finite energy-basis coefficients. Centering
removes every coefficient at the ground energy; the two Gaussian-tail
bounds and Parseval give the two vector errors. Moving adjoints across
the inner products gives the actual scalar commutator limit and the
ordinary centered-correlation error, without assuming either comparison.

Centering an arbitrary supported observable at the actual nonzero MPS
vector preserves its support and increases its norm by at most two.
Dividing by the actual squared vector norm therefore gives ordinary
connected correlations of arbitrary supported observables. Neither the
vector nor the observables are assumed normalized.

Finally set a=1, v=8e, T=ell/(2v), and q=T Delta. Both Gaussian errors
decay as exp(-ell Delta/(4v)); the short-time propagation term decays as
exp(-ell/2). The explicit Gaussian normalization and elementary
square-root absorption yield common positive constants K,kappa with

    |<AB> - <A><B>| <= K (|X|+1) ||A|| ||B|| exp(-kappa ell)

for 1<=ell<=d(X,Y), uniformly over every path parameter and ring length
N>=2. All inputs to this conclusion are the actual physical path,
supported observables, and disjoint nonempty supports. No spectral-filter
comparison, propagation estimate, clustering estimate, transfer bound,
or minimal-gauge choice is supplied as a public premise.

Passing finite correlations to limiting transfer contractions and minimal
gauges remains separate. No locality of the sharp spectral part and no
full SPT converse are asserted here. Issue #9879 remains open until the
remaining argument and integration are complete.

No local Lean command, build, elaboration or checkdecls was run, as
requested. Blueprint entries remain notready pending hosted acceptance.
Independent source/API reviews found no concrete mathematical mismatch.
First hosted diagnostics exposed elementary name, set-membership and
coercion-normalization issues in the foundations; these are source-repaired.
Native source/import/prose/format/integrity checks do not replace Lean
verification of the new clustering assembly.

## Hosted diagnostics on `7a2b4f351`

Job `123583214172` compiled the repaired Gaussian frequency rate and sharp
negative-frequency ground-covariance modules. Its remaining failures were
the generic real-to-complex integral rewrite and the two additive-bound
orientations in observable centering. Normalization now applies the
specialized complex integral identity directly after changing the endpoint.
The centering estimates use explicit two-term addition monotonicity. The
rate module's reported unnecessary tactic sequencing is also removed.
No mathematical statements changed and no local Lean command was run.

## Verified-head diagnostics on `5df07c430`

Job `123592310784` records `PR_HEAD_SHA` exactly as
`5df07c430bfd60f6a00d9eb4b6c411426590ccb7`. It compiles observable
centering, the Gaussian frequency rate and sharp ground covariance. Its
only primary failure is the namespace of the specialized complex integral
identity: the pinned declaration is global, so the proof now uses
`_root_.integral_complex_ofReal`. No local Lean command was run.

## Downstream transform diagnostics on `7d3a109db5`

Job `123604215169` records the child PR head exactly as
`7d3a109db55e51cabc3da978af6cd4147fff16db`. It reaches the actual transform
and reports an opaque uncurried integrand in the joint-integrability bound,
and a final simplification that rewrites the inverse variance only on one
side. The bound now changes directly to the two-variable integrand before
using its norm identity. The final argument identifies only the probability
tail with the cutoff, retaining the original actual time variance and its
normalization throughout the integral. Reported unused simp arguments are
removed. No statement or parameter changes; no local Lean command was run.
