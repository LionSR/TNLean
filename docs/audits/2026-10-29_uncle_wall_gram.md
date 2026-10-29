# Moving-wall finite Gram calculation

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

Remaining source steps are the two-wall Gram factorization error bound
and strict positivity of the limiting coefficients outside proper algebraic
exceptional sets. These identities do not assert Theta(N^2), an energy
bound, genericity, or gaplessness. Finite nonnegativity alone does not
supply a strictly positive asymptotic coefficient.

Validation: no local Lean build, elaboration, or checkdecls was run, at the
user's request. New Blueprint entries remain `notready`. Native source,
import, prose, line-width, and integrity checks are run separately. An
independent exact rational complex calculation with rectangular 2-by-1
walls compares the explicit coefficient sums against both matrix
recurrences and the scalar weighted formula at lengths zero through five.
This finite calculation is mathematical evidence, not Lean acceptance.
