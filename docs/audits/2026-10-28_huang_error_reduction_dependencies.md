# Gaussian error reduction for general one-dimensional Hamiltonians

This is a comparison of the published argument with the declarations available at
origin/main `856cfe29955d1192c956626632695bc4d8b40587`. It records missing mathematics; it
does not assert that unrestricted constructive error reduction has been formalized.

## Published construction

[Huang, arXiv:1406.6355v6](https://arxiv.org/pdf/1406.6355v6), Section 5.4, equations
(19)–(22) and Lemmas 18–19, uses, for $0<\eta\le1$ and $\Delta>0$,

$$
 A=\exp\!\left(-\frac{a(H-E')^2}{2\Delta^2}\right)
   =\int e^{-it(H-E')}\,d\gamma_{a/\Delta^2}(t),
 \qquad a=4\log(1/\eta)+24,
 \quad |E'-E_0|\le\Delta/\sqrt a.
$$

The filter improves a sufficiently accurate witness's energy. Truncation in time,
discretization, and an MPO approximation of each propagator produce one finite-bond
operator approximating $A$ in operator norm. The time cutoff has order
$\sqrt{a\log(1/\varepsilon)}/\Delta$. The propagator approximation has bond exponential
in time and polynomial in length and inverse error, using
[Osborne's one-dimensional evolution theorem](https://arxiv.org/abs/quant-ph/0508031).
Thus the construction is polynomial at inverse-polynomial precision for fixed gap, with
no restriction that the total ground energy be bounded independently of chain length.
Huang's overview and Lemma 3 explicitly retain ground-energy dependence in the earlier
LVV randomized estimate. This Gaussian argument is a subsequent replacement for that
step, rather than a proof of its unrestricted printed polynomial estimate.

## Available declarations

| Required ingredient | Existing result | Remaining distinction |
|---|---|---|
| Gaussian integral and its spectral multiplier | QICLean `GaussianFilter.gaussianIntertwiner`, `inner_gaussianIntertwiner` in `Analysis/GaussianFilter/MatrixIntegral.lean` | The integral can be specialized to $H-E'$ and a scalar zero generator. |
| Norm and time-tail bounds | QICLean `norm_gaussianIntertwiner_le`, `norm_gaussianIntertwiner_sub_truncated_le` | Already dimension independent in the matrix operator norm. |
| Exact-centered spectral gap estimate | QICLean `GaussianFilter.norm_sub_ground_le_of_coefficients`; TNLean Hastings `norm_gaussianTimeAverage_sub_groundProjector_le` | The latter assumes ground energy zero. It is not the approximate-center energy estimate of Huang's Lemma 18. |
| Scalar energy shifts | QICLean `Matrix.hermitianUnitaryPath_add_smul_one`, `GaussianFilter.gaussianIntertwiner_add_smul_one`; TNLean `Matrix.IsGappedGroundState.sub_smul_one` | These give algebraic shifts, without selecting an energy estimate before the ground vector. |
| Stability of unitary evolution | QICLean `Matrix.norm_hermitianUnitaryPath_sub_le` in `Analysis/UnitaryEvolution.lean` | Together with scalar multiplication of the generator, this gives the time Lipschitz estimate needed for quadrature. |
| One-dimensional localization | TNLean `norm_heisenberg_sub_siteExpectation_chainNeighborhood_le` in `MPS/AreaLaw/LiebRobinson.lean` | Explicit bound of the form $C|S|^2\|B\|e^{v|t|-\ell/2}$; adequate for logarithmic buffers at fixed interaction range and strength. |
| Supported relative evolution | TNLean `QuantumCircuit.exists_supported_projected_relative_evolution` | Constructs the local unitary path and bounds its error by $|t|$ times a generator-localization error. |
| Supported Gaussian averaging | TNLean `QuantumCircuit.exists_supported_gaussian_integral_of_projection_bounds`; Hastings `exists_supported_interactionAverage_approx` | These localize a relative evolution or an interaction-picture average. They do not represent the full propagator as a polynomial-bond MPO. |
| Algebraic operator decompositions | QICLean operator-Schmidt decompositions; TNLean two-marker and selected-middle MPO families | These supply useful finite-dimensional algebra. Their present statements are not a global real-time propagator approximation in operator norm. |

Searches of the production TNLean and pinned QICLean analysis sources found no theorem
constructing finite Gaussian quadrature with an explicit number of nodes, and no theorem
approximating the full one-dimensional propagator by one MPO with the required norm and
bond estimates. The existing Gaussian probability sampling statements concern different
operators and do not fill either requirement.

## Concrete missing theorems

The following is a proposed dependency order, inferred from the available declarations.

1. **Finite weighted quadrature in operator norm.** For a unitary path with Lipschitz
   constant $M$, truncate the Gaussian measure to $[-T,T]$, partition into intervals of
   diameter at most $\tau$, and use each interval's Gaussian mass as its nonnegative
   weight. The quadrature error is at most $M\tau$ and the weights sum to at most one.
   The existing tail estimate pays for the omitted times. Unlike an unquantified
   finite-sum existence statement, the theorem must bound the number of intervals by
   $O(1+T/\tau)$ and retain the weights and nodes before the ground vector.
   This choice of weights changes Huang's displayed rectangular quadrature, while
   preserving the finite-operator existence argument and its polynomial term count.
   With $M\le\|H-E'I\|=O(L)$, take $\tau\le\varepsilon/(3M)$, reserve
   $\varepsilon/3$ for the tail and $\varepsilon/3$ for the propagator errors, and obtain
   $O(1+TL/\varepsilon)$ terms. Exact interval masses suffice for this existence
   theorem. An assertion about computing the coefficients to a prescribed accuracy
   would require an additional numerical approximation theorem.

2. **A global block-unitary approximation to time evolution.** Partition the chain into
   contiguous blocks. Evolve independently inside blocks, and correct across their
   boundaries using projected relative evolutions supported in disjoint boundary
   neighborhoods. Prove the comparison with the full evolution, summing the localization
   errors over boundaries. The required conclusion is one operator with a two-layer
   local-unitary presentation, error at most $\varepsilon$ and block width
   $O(v|t|+\log(L/\varepsilon))$. The existing ODE comparison and chain localization
   estimates are the principal analytic inputs. This assembly is not presently a
   theorem of the library.

3. **Bond bounds for that same operator.** Derive a simultaneous bound across every cut
   from the two-layer presentation, of the form $q^{O(\ell)}$. Sum the finitely many
   propagator approximants using a direct-sum bond construction. A separate low-rank
   approximation at each cut does not establish the existence of one operator with
   all the asserted bonds and the same operator-norm error. A conversion through
   Hilbert–Schmidt error would require control of a potentially exponential dimension
   factor and does not supply the desired result automatically.

4. **Approximate-center filtering and normalization.** Extend the existing
   exact-centered spectral estimate to an energy guess within
   $\Delta/\sqrt a$. Bound the retained ground amplitude below and the excited
   contribution above, then include the operator-norm approximation error before
   normalizing. For energy error, the required error budget includes the factor
   $\|H\|=O(L)$; overlap error can instead be estimated directly from the orthogonal
   component. The current size-and-bond theorem supplies overlap $1/2$; Huang's printed
   Lemma 18 uses $19/20$, so its numerical constants cannot simply be copied onto that
   theorem. The spectral argument must be proved with the actual available input
   overlap or the preceding constants must be sharpened.

5. **Energy guesses and viable families before the ground vector.** Choose a finite
   energy grid on a known interval containing the spectrum, with spacing at most
   $\Delta/\sqrt a$. Its size is polynomial for fixed gap. Take the union of the
   left-action families for all guesses, and prove that an appropriate guess exists
   for each ground energy. The existence of one filter chosen using the exact ground
   energy would not preserve the quantifier order of the successive viable-set goal.

The quadrature mesh can have inverse-polynomial size because the shifted generator's
norm is $O(L)$. The time cutoff is logarithmic in $L$ at inverse-polynomial target error
and fixed gap. Consequently the proposed block width is logarithmic and the resulting
bond is polynomial. These are parameter calculations for the proposed construction,
not substitutes for the missing norm, support and common-operator theorems above.

## Subsequent quadrature contribution

The separate local contribution recorded in
[the Gaussian quadrature audit](2026-10-28_huang_gaussian_quadrature.md) supplies the
first stage, including the interval masses, endpoint treatment, mesh error, Gaussian
tail and explicit node count. It also derives the Lipschitz estimate for the actual
Hermitian propagator. Both modules and their imported foundation fixture passed strict
separate-module checks. Ordinary build and blueprint gates remain pending, and the
generic mathematics is identified for QICLean ownership. The global propagator/MPO
construction, filtering with an approximate energy center and the energy-grid family
remain independent missing stages.
