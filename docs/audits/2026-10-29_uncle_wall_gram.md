# Moving-wall Gram and generic slope calculation

Source: arXiv:1210.6613, `Papers/1210.6613/UncleHMPS.tex`, proof of
Lemma `lemma:lowenergystates`, especially lines 1230–1265. This is one
finite component of #10286, stacked on the actual trial in #10316.

The source trial has two independent moving windows with N+1 positions
each. The new module uses the existing `uncleDomainWallWord` inside those
windows. It does not define another trial vector or replace its norm by
an assumed sequence.

For the first wall, the source unital normalization is
`Kraus.mapLM B 1 = 1`, namely sum B_i B_i* = I. The left stationary density
satisfies `Kraus.adjointMap A rho = rho`. These are the unital and dual
stationary conventions in the source normalized standard form; they are
not trace-preserving normalization of the same transfer orientation.
The identities allow arbitrary dimensions, including empty index types.
Faithfulness and unit trace of the density are unnecessary for these finite
identities and are not added as hypotheses.

`UncleWallGram.lean` defines the actual correlation Z_n and Gram matrix
Y_n by sums of coefficient products. It derives:

- Z_0 = Y_0 = 0 and finite positive semidefiniteness of Y_n;
- Z_(n+1) = F(Z_n) + C, with C = sum R_i B_i*;
- Y_(n+1) = E_A(Y_n) + J(Z_n) + J(Z_n)* + G;
- nonnegative weighted Gram trace for every positive density;
- the stationary Hermitian scalar recurrence for eta_n = tr(rho Y_n);
- the exact finite formula
  eta_(n+1) = (n+1)c_0 + sum_(k<n) (n-k)
  [ell(F^k C) + conjugate(ell(F^k C))].

Here F is the existing rectangular mixed Kraus map, G = sum R_i R_i*,
J(X) = sum A_i X R_i*, and ell(X) = tr(rho J(X)). Thus all scalar
coefficients are contractions of the actual tensors. At lengths one and
two the formula gives c_0 and 2c_0 + 2 Re ell(C), respectively.

`UncleWallGramAsymptotics.lean` additionally proves convergence of the
actual mixed series under `Kraus.mixedMapSpectralRadius A B < 1`, using
QICLean geometric power decay and Mathlib's summable comparison test.
The exact Gram increments converge to the explicit coefficient obtained
by contracting that series. Mathlib Cesaro convergence then gives
eta_n / n tending to that coefficient. This uses the source spectral
radius condition, not the stronger operator-norm-below-one condition.
No positivity or nonvanishing of the limiting coefficient is assumed.

`UncleWallGramSlopePositive.lean` derives nonnegative slope from the actual
normalized Gram limit for a positive stationary density. It also gives a
genuine positive case: when C = sum R_i B_i* vanishes and R is nonzero,
the slope equals tr(rho sum R_i R_i*) and is strictly positive for a
positive definite density. A physical coefficient c annihilating the
adjoint B letters constructs R_i = c_i M for a nonzero rectangular M.
Such a c exists by a dimension argument whenever d > b^2. Full source
perturbation span gives d >= (a+b)^2 > b^2 for a > 0, so this dimension
condition is available in the source setting. The resulting positive
witness is a value somewhere in wall space; it is not asserted to retain
the full perturbation span. There is no assumed positive-slope premise.

`UncleWallGramQuadratic.lean` packages the actual slope as a real
quadratic form. The correlation series is complex linear in R by
summability and the infinite-sum linearity lemmas. Its explicit real
bilinear contraction has diagonal exactly equal to the actual slope's real
part. Under source normalization it is nonnegative, and the positive
witness proves it is not identically zero.

`UncleWallGramGeneric.lean` derives the zero set as the radical of that
nonnegative quadratic form. Its radical is proper, its positive complement
is open and dense, and its zero set has zero additive Haar measure by the
existing Mathlib proper-subspace theorem. The almost-everywhere positivity
statement is thus proved from the actual quadratic exceptional set; it is
not an assumed genericity condition. A full perturbation witness for the
fixed A/B blocks is used only to derive the dimension bound and nonidentity.
The explicit positive witness itself need not retain perturbation span.

The pair-space theorem uses one additive Haar measure on the space of
(R,L), with no independence or product-measure premise. Its exceptional
set lies in the union of the first radical times the whole second wall
space and the whole first wall space times the second radical. Both are
proper real submodules and therefore Haar-null. The single full
perturbation witness supplies both physical-dimension bounds. The strict
mixed-transfer conditions are stated in both orientations, as supplied by
the source off-diagonal damping lemma for distinct normalized blocks.

`UncleWallGramBounds.lean` derives a uniform bound on the actual weighted
Gram norm by C*n from the normalized limit, absorbing the finite initial
segment. For a faithful density, the existing QICLean positive lower bound
rho >= c*I gives tr(Y_n).re <= K*eta_n.re. This yields uniform linear
bounds on the actual unweighted Gram trace and its Euclidean operator
norm, suitable for the pinned endpoint estimates. No growth estimate is
introduced as a hypothesis.

Remaining norm work is the actual two-wall Gram factorization error bound. These identities do not assert Theta(N^2), an energy
bound, genericity, or gaplessness. Finite nonnegativity alone does not
supply a strictly positive asymptotic coefficient.

Validation: no local Lean build, elaboration, or checkdecls was run, at the
user's request. New Blueprint entries remain `notready`. Native source,
import, prose, line-width, and integrity checks are run separately. An
independent exact rational complex calculation with rectangular 2-by-1
walls compares the explicit coefficient sums against both matrix
recurrences and the scalar weighted formula at lengths zero through five.
This finite calculation is mathematical evidence, not Lean acceptance.
An additional exact scalar-block example checks full four-letter perturbation
span and derives the actual slope as |R_0+R_1|^2+|R_2|^2+|R_3|^2. Its real
quadratic matrix has rank six and is positive semidefinite, with a positive
zero-seed wall witness.
