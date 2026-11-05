# Actual Hermitian MPOs for finite regional soft replacements

The theorem constructs the operator

    G = H + z I + sum_j [epsilon_j I + h_(m,t)(R_j-epsilon_j I) - R_j]

from one original nearest-neighbour Hermitian interaction family, regional
bond-label sets, and explicit lower energies epsilon_j I<=R_j. The scale
and Taylor order are independent with t>=3m and m>=1. The real scalar z is
represented exactly; choosing it to remove the regional scalar reference
is permitted without omitting that scalar from the operator identity.

For s regions, define delta=xi/max(1,s), W=t 2^(m+1) and the common explicit
logarithmic cluster order r. With D0=1+Nq^2, the constructed MPO has bond

    D = D0 + 2s[D0+(m+1)r^2q^r].

Both G and its actual represented approximant are Hermitian, and their
operator-norm distance is at most xi. The result permits s=0, empty regions,
N=0 and q=1. The label sets may overlap; the stated operator formula is
retained literally. Disjoint regions give the usual simultaneous replacement.

Every regional approximant is constructed from the original interactions,
then replaced by its actual represented Hermitian part without increasing
its error. An exact local-sum MPO for (1-s)H+zI completes the finite sum.
The identity G=(1-s)H+zI+sum_j F_j and s*delta<=xi give the bound. No regional
MPO, cut rank, successful sampling event or spectral comparison is supplied.

For fixed q, log D is O_q(m+log_+t+log(N+1)+log(s+1)+log_+(1/xi)). Thus
logarithmic order, polynomial scale and region count, and inverse-polynomial
accuracy give polynomial bond. The dependence on every varying parameter
is retained. This is an operator-representation auxiliary for ALVV,
arXiv:1602.08828v2, `t:aisefficient` and `t:aisgaplessefficient`, lines
1373–1392 and 1435–1442. Regional energy estimation, simultaneous low-energy
comparisons, the actual filter and GEN are subsequent steps. No small norm
of the uncentered G or computational running time is claimed. The corrected
interaction-label construction does not restore the false printed cluster
estimate; its existing counterexamples and gap note remain unchanged.

All outputs are temporary; no provider or dependency cache was changed and no
Mathlib source was rebuilt.

The mathematical book entry is included. Ordinary integrated full-build
and complete-book checks remain pending. Foundation commands stay under
a temporary directory; no Lean test fixture is added.
