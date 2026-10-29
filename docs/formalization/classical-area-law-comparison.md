# Six approaches to one-dimensional area laws and ground-state approximation

An entropy bound, an approximation by a matrix product state, and a procedure that
constructs such an approximation are distinct conclusions. An area law bounds the
entropy across a cut. A global MPS approximation requires simultaneous control of
the discarded Schmidt weights at all cuts. A construction by viable sets must also
bound the intermediate families and choose them without knowing the ground vector.
A running-time theorem requires further effective and numerical estimates.

The six sources considered here are the following. The table describes the
mathematical method of each source, rather than asserting that its entire argument
has been formalized.

| Source | How the spectral information is used | Principal conclusion or distinction |
|---|---|---|
| [Hastings, *Solving Gapped Hamiltonians Locally*](https://arxiv.org/abs/cond-mat/0508554) | Gaussian filtering and locality turn Hamiltonian terms into approximately local terms that almost preserve the ground state separately. | A local projective description and generalized MPS representation; no bound on intermediate dimensions is asserted, and the setting is not confined to a chain. |
| [Hastings, *An Area Law for One Dimensional Quantum Systems*](https://arxiv.org/abs/0705.2024) | A local factorization of the ground projection feeds an entropy argument at doubling scales. | An area law and Schmidt-tail estimates, which yield a global MPS approximation. |
| [Schuch–Wolf–Verstraete–Cirac](https://arxiv.org/abs/0705.0292) | Entropy conditions are compared directly with Schmidt tails, without deriving those conditions from a Hamiltonian gap. | A von Neumann area law alone does not ensure efficient MPS approximation; suitable Rényi control gives a stronger sufficient condition. |
| [Arad–Kitaev–Landau–Vazirani](https://arxiv.org/abs/1301.1162) | Chebyshev polynomials suppress excited energies while a separate argument controls the resulting Schmidt ranks. | A sharper area law and subpolynomial bond dimension, with a subexponential approximation algorithm. |
| [Landau–Vazirani–Vidick](https://arxiv.org/abs/1307.5143) | Extension, boundary-net size trimming, bond trimming and error reduction maintain viable sets at successive cuts. | A construction of a succinct approximation to the unique ground state, rather than only existence of a low-bond vector. |
| [Arad–Landau–Vazirani–Vidick](https://arxiv.org/abs/1602.08828) | Viable subspaces, sampling, truncation and error reduction treat a target space; merge constructions organize the approximation. | Degenerate ground spaces and low-energy spaces under a density condition; the algorithms require additional quantitative constructions. |

The distinction between entropy and tails is essential. A uniform bound on von
Neumann entropy can coexist with poor approximation at fixed trace distance, as
shown by Schuch–Wolf–Verstraete–Cirac. In the existing TNLean chain proof, entropy
and MPS approximation are parallel consequences of a marginal tail estimate. The
MPS proof uses one sequential truncation of the state. Independent approximating
vectors at separate cuts would not by themselves produce that conclusion.

The Hastings development constructs a physical approximate factorization and
proves the entropy bound through the source's mutual-information and doubling
argument. A numerical Lieb–Robinson estimate applies to arbitrary finite supports.
Writing $c_R=2(R+1)2^{2R+1}e^{2R}$, the pair $V=40c_RJ$, $\xi_C=80$ gives
$\Xi=\max(2V/\Delta,80)$. At this admissible enlarged length the entropy is at
most $c_0(6\Xi)\log(6\Xi)\log q\,2^{(6\Xi)\log q}$, with $c_0$ depending
only on the range. This recovers the printed shape by a valid choice of the
existential source parameters. The factor of two in the doubling exponent at a
fixed smaller length remains necessary. The length convention and positivity
qualifications are recorded in `docs/paper-gaps/hastings07_lemma1_decay_length.tex`,
`hastings07_relent_constants.tex` and `hastings07_doubling_constants.tex`.

For Hastings' 2006 programme, the local truncated filters and thermal truncated
exponentials are constructed from the interactions. On a physical ring, an
actual rounded grouping assigns the filtered terms to neighbouring pairs,
including the closing pair. The spectral hierarchy is then constructed through
all binary levels, with an additional window for the closing edge. Under the
local residual estimate assumed at the beginning of the source's Section III,
a nearby unit vector belongs to every retained descendant space. The original
Hamiltonian gap bounds every orthonormal family in the final retained space
by twice the rank of the original ground projection. In the unique-ground-state
case, the local residual is derived directly from the original spectral gap;
no pair family or residual estimate is supplied. The final retained dimension
is at most two. The spectral-window centres depend on expectations in the
specified ground vector. The corrected deficiency recurrence is retained.
Membership in these spectral spaces does not itself give tensor coefficients
or intermediate bond bounds.

The ground-space basis argument now constructs the spectral refinements in
arbitrary finite dimension. A non-scalar compression gives a proper spectral
split; scalar terminal spaces need no further separation. Both cross terms
are retained, giving decay rate $\gamma/2^n$ for ground-space dimension $n$.
For the full-Hamiltonian filtered local terms, summation gives a bound independent
of the number of sites when the ground-space dimension, local norm budget,
gap and polynomial sphere-growth constants are fixed. The unrestricted metric
claim is false on bounded-degree trees. The corresponding mathematical
counterexample and the geometric qualification are recorded in
`docs/paper-gaps/hastings05_tree_basis_counterexample.tex` and
`hastings05_geometric_growth_scope.tex`. The locally truncated basis theorem, the assembly of actual retained-space
coordinates into tensors, and the thermal index bound in terms of a local
radius remain separate obligations. The source explicitly makes no claim
of bounding the intermediate matrix-product dimensions (lines 104–109);
its retained-basis expansion is in Section III, lines 630–685.
An additional bound on those dimensions would be a further result.

For the viable-set construction, the relevant quantifier order is different. The
family at a cut is selected from the Hamiltonian and the preceding family before
the ground energy and ground vector are supplied. Its viability is then asserted
for every ground pair satisfying the gap assumption. A theorem that first fixes
the ground vector and then chooses a suitable finite family would omit an essential
part of this construction.

The finite physical filter used in the present development follows
[Huang, Section 5.4](https://arxiv.org/abs/1406.6355v6). Energy estimates fill a mesh
in the fixed interval from minus the chain length to the chain length. The Gaussian
approximation is constructed at every estimate. A suitable member is close to a
positive multiple of the ground projection with amplitude at least one half.
Taking a union of all left factors gives error reduction without knowing which
estimate is suitable. The resulting bounds are polynomial in length at fixed local
dimension, gap and precision constant. This supports the LVV successive-family
argument, but does not establish the sharper printed rates or a running-time bound.

A product-ancilla argument now gives arbitrary accuracy from that same successive
construction. For fixed local dimension $q\ge2$ and gap lower bound $\Delta>0$,
the polynomial coefficient and degree are chosen before both length $L$ and
integer accuracy parameter $R\ge1$. The original chain is extended to
$N=L+2R^2$ sites with actual on-site penalties whose product ground state and
gap lower bound one are proved. The padded gap lower bound is $\min(\Delta,1)$, independent
of $R$. One padded successive run is chosen before the original ground pair;
a phase-aligned unit vector in its actual stage-$L$ retained span has squared
error at most $R^{-2}$ and MPS bond bound $P(N+1)^d$. All intermediate families
retain uniform polynomial size and bond bounds. This is an additional
consequence of the corrected construction, rather than a claim of the printed
LVV rates or a computational running-time theorem.

Several quantitative distinctions must remain visible when comparing the proofs.
The size-trimming estimate uses the library's constant-cut bond bound and corrected
matrix-net exponent. Independent bond trimming requires the documented quadratic
radius. The unrestricted power-sampling estimate cannot be read as a polynomial
bound with a degree independent of the ground energy; the published LVV version
records that dependence. These points are documented in the corresponding
`docs/paper-gaps/lvv13_*.tex` notes.

The ALVV, LVV and AKLV constructions use one pinned companion revision,
preserving the matrix Bernstein theorem. The low-energy, entropy and
interpolation results are compiled together.

The AKLV polynomial rank estimate now applies to the original supported
Hamiltonian, with no supplied tensor decomposition or rank hypothesis. For a
window of width $s>0$ and a polynomial of degree at most $\ell$, the rank at the
central cut is at most
$[q(\ell+1)]^{16(\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1)}$.
For $\ell\ge1$, the source base $q\ell$ is available with exponent
$96\max(\lfloor\ell/s\rfloor,\lfloor\sqrt\ell\rfloor)$.
The commuting-gap count includes the documented correction. An actual Chebyshev
polynomial of the same supported Hamiltonian has both this rank bound and its
spectral suppression estimate. The two exterior truncations are also constructed
from the original positive-contraction interactions, with genuine regional minima
and normalized energy $E_0\in[0,6]$. For windows of at least six interactions,
$t\ge1024+16\log(1/g)$ gives an actual truncated gap at least $9g/10$ and a
phase-aligned unit ground vector with squared error at most $e^{-t/16}/100$.
The earlier polynomial sufficient threshold remains a corollary.
The original gap bound $g\le1$ is derived from the physical hypotheses.
The local support and middle-normalization corrections, and the finite-window
restriction, are recorded in `docs/paper-gaps/aklv13_two_block_robustness.tex`.
For the actual clipped Hamiltonian, its positivity and ceiling $2t+s$ are derived
from the original terms and reference minima. At the same original central cut,
the actual degree-$\ell$ Chebyshev polynomial has amplitude at most
$2\exp[-2\ell\sqrt{(9g/10)/(2t+s)}]$ and rank at most
$[q(\ell+1)]^{32(\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1)}$.
No spectral ceiling, projector gap or spatial decomposition is supplied.
A universal scalar choice now sets $s=\lceil Au^2/g\rceil$, degree $s^2$ and
$t_0=1024+16\log(1/g)$, where $u=1+\log q+\log(1/g)$.
Its actual rank budget and squared shrinking coefficient satisfy
$D\delta\le10^{-5}<1/256$, and $\log D\le C u^3/g$ with an explicit
constant. An exact normalization theorem constructs the phase-aligned output of a filter
with nonzero target overlap, with its residual-to-overlap error and actual
Schmidt-rank growth. For an available selected window, the physical favorable
filter and its initialization are now constructed. The product vector targets
the actual clipped ground vector $\phi_{t_0}$, with overlap at least
$1/\sqrt{2D}$. The phase-normalized filtered product has cut rank at most $D$,
squared distance at most $1/64$ from $\phi_{t_0}$ and at most $1/16$ from
$\Omega$. The small product overlap is not transferred directly to $\Omega$.
For every fitting window of at least six interactions, every threshold and
chosen degree, a further physical refinement constructs the actual polynomial
and its phase-normalized image of a unit input close to $\Omega$. It retains
the variable-window rank bound and the contraction
$\|\psi-\phi_t\|^2\le8\Delta\|x-\phi_t\|^2$, with
$\|\psi-\Omega\|^2\le16\Delta+e^{-t/16}/50$.
The coherent moving-ground-state recursion is now constructed from the actual
successive filtered states, with the initial product-overlap cost retained.
Accuracy-dependent windows also include exact boundary and short-chain
alternatives. Their original square-root polynomial degree gives a uniform
rank bound and actual Schmidt tails at every cut. With
$u=1+\log q+\log(1/g)$ and
$z=\log(2048(L+1)/\epsilon^2)$, the actual normalized ordered product of
leading regional spectral projections is an MPS at distance at most
$\epsilon$, with
\[
 \log D\le C\left[\frac{u^3}{g}
  +\left(\frac{z^3}{g}\right)^{1/4}(u+\log(z+1))\right].
\]
The universal constants precede the chain, gap and accuracy. The physical
hypotheses derive $q\ge2$ and $g\le1$, independently of a fitting window.
The actual first-excited-energy hypothesis remains explicit. No independent
MPS-existence theorem is used. The same actual filter sequence also gives
finite dyadic tail bounds and the entropy estimate
$S_k(\Omega)\le Cg^{-1}(1+\log q+\log(1/g))^3$ at every cut.
Exact smaller-side dimension bounds cover endpoints and chains where the
initial window does not fit. The constant precedes all physical data.
The actual first-excited-energy qualification remains explicit here as well.

For a unique ground vector on an open chain with $q\ge2$ and $0\le h_j\le I$,
the gap is at most one. An endpoint unitary with zero expectation in that vector
gives an orthogonal unit trial vector; it changes only one bond, whose expectation
can increase by at most one. This proves the normalization stated in AKLV,
Section 5, before equation (4), and is formalized by
`gap_le_one_of_positive_nearest_neighbor_terms`. Orthogonality to one chosen ground
vector does not imply orthogonality to an entire degenerate ground space, so this
argument must not be used to remove the capped-gap qualification below.

For a degenerate target space, uniformity must cover every unit vector of the full
physical ground eigenspace. The coefficient of its logarithmic dimension is part
of the theorem. The checked ALVV development retains coefficient one on this term,
uses an actual interval entropy, and builds one normalized global MPS through
sequential truncation. Its quantitative bound uses the capped gap
$g=\min(\gamma,1)$; a claim with the uncapped gap requires an additional argument.
The source's degenerate-ground-space assumption includes a second spectral value,
so the existence of an excited spectrum should be distinguished from an extra
hypothesis imposed by a formalization.

For frustration-free projection chains, the actual even/odd detectability operator
is now constructed. Its noncommutation count is derived from the physical bonds.
It fixes the full ground kernel and preserves its orthogonal complement, and the
converse estimate holds for every unit vector with constant three. An actual
spectral gap above the entire zero-energy kernel gives the homogeneous squared
contraction factor $4/(4+\gamma)$, for arbitrary kernel dimension and without
a gap cap. Replacement of arbitrary positive contraction terms by their actual
range projections now preserves the bond supports and the full original kernel,
and increases the Hamiltonian in operator order. The same contraction follows
with the original gap. The regional truncated Hamiltonian is now constructed
from the actual outside bonds and internal parity products. It is positive,
has exactly the full original kernel, and its internal replacement has norm
at most two. Its nonzero spectrum is now bounded below by
$\gamma/[3(4+\gamma)]$, using the original physical detectability product
on the common full-kernel complement. No uniqueness or upper-gap assumption
is added. The actual regional truncation now also has operator Schmidt rank
at most $q^2+3$ at every cut, derived solely from the original nearest-neighbour
supports. No decomposition or rank hypothesis is supplied. The printed regional rank bound
$d^2+2$ also needs an additive correction: an eight-qubit example with unique
ground and gap one has rank seven at the middle cut. The corrected general
bound is $d^2+3$, documented in
`docs/paper-gaps/alvv16_frustration_free_truncation_rank.tex`. This exact
mathematical counterexample is not a Lean theorem.

The global approximation also gives one $r$-dimensional reference space,
mutually $\varepsilon$-close to the full physical ground space, whose every
vector has bond bound $r^2B$. This reference is chosen before the viable space
to be trimmed. Collective trimming now treats arbitrary intervals in their
actual tensor coordinates, with the entire exterior retained. At an internal
cut of a region, the common reference gives the two-boundary bound
$D_{\mathrm{ref}}^2$, where $D_{\mathrm{ref}}=r^2B$.
The trimmed space has dimension at most the original dimension $s$ and
internal cut rank at most $s/\xi^2$; its error is
$4\delta+6\varepsilon+4\xi\sqrt{(\ell-1)D_{\mathrm{ref}}^2}$.
Adjacent child spaces merge in the actual coordinates of their union, with
dimension at most the product of their dimensions and viability error
at most the sum of their errors. The target remains the same possibly
entangled full global ground space. A long-parent theorem now composes these operations with the literal Haar
sample and actual powered operator family. Its measurable event is defined
for fixed child spaces; every successful unitary gives the actual sampled
word image and collective trim, of dimension at most $D^6s^3$ and viability
error at most $3/200$ for the original full ground space. The target and
improving family precede the child spaces and sample size. The corrected
complex net exponent is $2r$, where $r$ is the ground-space dimension.

The sample size can be chosen uniformly: for $D\ge2$, $r\ge1$ and
$0<\beta\le1$, put
$A=1+\log r+\log D+\log(1/\beta)$ and
$s=\lceil4096rA\rceil\le4097rA$.
For every merged dimension $Q\le D^{12}s^6$, the failure estimate is at most
$e^{-s/64}\le\beta$; if $Q\le s$, the sample is the entire merged space
and the failure is zero. The recursive tree and an adaptive joint probability
law remain separate obligations.

The power-filter application constructs one actual sample with both norm estimates,
all letter-count bounds, and every spatial rank bound $\ell q^{2u}$.
At a specified energy, the sample and its cut factors precede every unit vector
in the ground line and every viable input family. A further scalar-free theorem
uses a supplied width-one bracket $[a,a+1]$ and chooses its word length and sample
budget before the actual energy as well. With $n$ equal to the number of terms
plus one, it uses $m=\lceil(n-a)\log Q/\Delta\rceil$ and retains the cost
$n^2\exp(4(a+1)\log Q/\Delta)$. The actual unscaled sample $T$ approximates
$\beta P_0$ to relative error $\eta+1/Q$, with
$\beta=(1-E_0/n)^m>0$; its same cut factors give the size, bond and viability
bounds. A separate theorem retains the actual two-level product-uniform
sampling law and proves simultaneous success probability at least
$1-1/(2L^3)$, hence at least $1-1/L^3$, for its explicit sample counts.
This probability theorem fixes the ground energy first. Choosing the bracket
without that energy and completing the running-time argument remain separate.

The [published Methods section](https://people.eecs.berkeley.edu/~vazirani/pubs/1dalg.pdf)
states the energy-dependent complexity exponent and permits omission of the
unknown overall scalar after output normalization. Its advertised uniform
polynomial case has bounded ground energy. The bracket theorem retains that
energy dependence; it does not supply an energy-independent polynomial degree.

For low-energy targets, one actual clipped Hamiltonian supplies both buffered
spectral comparisons and a common polynomial improving family. The interior
family has at most $D^2$ terms with $D=(q\ell^2)^{20\ell}$.
The prescribed-interval construction now also treats short, empty and endpoint
intervals. It uses the common budget $D=(q\ell^2)^{22\ell}$, transports the
actual long-interval family to the prescribed region, and reuses configuration
matrix units on short regions. The family precedes every viable input subspace.
One constant at fixed density bandwidth is chosen before the chain and
Hamiltonian, with strict clipped-filter tradeoff $D^{12}\Delta<10^{-5}$.
The explicit source-scale count retains the logarithmic correction in
$\log L/\mu$ and absorbs the capped width into a density-bandwidth constant.

The clipped targets improve error to $\Delta/(1-\delta)^2$.
For the original windows the two spectral comparisons instead give
$2(\Delta/[1-2(\delta+\varepsilon)]^2+\varepsilon)$, assuming
$\delta\ge0$ and $2(\delta+\varepsilon)<1$.
With comparison error $1/200$, its additive contribution is already $1/100$;
a final $1/100$ claim requires retuning that precision.
The low-density induction requires sampling between distinct nested targets
and a dyadic rank estimate; the fixed-ground-space induction does not provide
it. The actual improving family can now be powered: the same target and
retained operators precede every integer power and viable input space.
Ordered words of length $k$ have cardinality at most $D_0^{2k}$ and
suppression $\Delta_0^k$. The logarithmic choice
$k=\lceil\log_{D_0}(D_0^2s)\rceil$ gives a polynomial output dimension
$D_0^6s^3$. When $D_0^{12}\Delta_0\le b<1$, the sampling-scale estimate
cancels the powers of $D_0$ and yields
$\Delta_0^k/c^2\le(1024/9)b/s^2$.
These are estimates for actual operator words, used by the sampled-parent
event above. The low-density induction between distinct nested targets is
still separate from that fixed-ground-space construction.

The scalar soft truncation is formalized with the corrected cap $t(1+\log m)$,
its polynomial and geometric remainders, and an exponential-weight estimate.
For $m\ge1$, $x\ge0$ and $0<\theta\le1/2$,
$x-h_{m,m}(x)\le(2/\theta)e^{\theta x-\theta m/2}$.
For every prescribed interval, the physical exponential moment on the whole
original closed window is now derived from the original nearest-neighbour terms:
$\|e^{(A_J-\varepsilon'_J I)/8}|_{G_\eta}\|\le5e^{(17+\eta)/8}$.
The regional minima and centered original ground energy are constructed before
$\varepsilon'_J$, $\eta$ and the vectors; the boundary count is at most two
and the centered ground energy is at most two. No gap or ground-space-rank
hypothesis is imposed. For equal order and scale, the constructed physical
soft Hamiltonian is Hermitian, lies below the original Hamiltonian, and satisfies
$\|(H-\widetilde H_{m,m})|_{G_\eta}\|\le80e^{(17+\eta)/8-m/16}$.
The reverse residual is also proved on the actual soft window, with bound
$80e^{(17+\eta+\alpha)/8-m/16}$, where $\alpha=(m/2)2^{-m}$ and
$m/2\ge17+\eta+\alpha$.
Both residuals use the same constructed regional minima and actual ground energies.
For $\eta,w,\delta>0$, put
$\rho=\min(1,w/2,\delta w^2/[2(\eta+2)])$ and choose
$m=\lceil35+2\eta+16\log(80/\rho)\rceil$ before all chain and Hamiltonian data.
The actual centered energies satisfy $0\le E_0-E_s\le\rho$, and both
directed spectral-subspace comparisons have accuracy $\delta$ after enlarging
the target ground-relative window by $w$. This covers one interval with equal
scale and order; it does not assert the printed gap prescription.

The same-matrix soft/hard inequalities also retain the source's approximate
minimum: if $A-\varepsilon'_J I\ge0$ and $r-10\le\varepsilon'_J$, then
$\min(A,(r+t/2-10)I)-(t/2)2^{-m}I
 \le\varepsilon'_J I+h_{m,t}(A-\varepsilon'_J I)\le A$.
This order statement is separate from closeness of physical spectral subspaces.
The companion library also proves an energy-normalized bound for the actual
finite alternating sum
\[
R_S^H(\beta)=\sum_{T\subseteq S}(-1)^{|T|}
  e^{-\beta(H-\sum_{i\in T}h_i)}.
\]
For Hermitian $H,h_i$, $\|h_i\|\le1$ on the finite set $S$,
$H\ge\lambda I$ and $\beta\ge0$, it gives
$e^{\beta\lambda}\|R_S^H(\beta)\|\le(e^\beta-1)^{|S|}$.
The lower energy may be negative. The proof derives the exact Duhamel
identity and its norm induction; no partition function is used.
A corrected tail now applies to the existing truncation on the actual path of
$N$ interaction labels. For Hermitian $h_i$, if $r>0$, $H=\sum_i h_i$, $\|h_i\|\le1$,
$H\ge\lambda I$, $\beta\ge0$, and $b=2(e^\beta-1)\le1$, then
\[
 e^{\beta\lambda}\|e^{-\beta H}-M_r\|
 \le e^{N^2b^r}-1.
\]
Here $M_r$ retains the exact-support terms whose path components have fewer
than $r$ labels. Inclusion--exclusion, interval-window geometry, the injective
minimum-label marker and the weighted component count are derived explicitly.
No commutation premise is needed for this norm estimate. The cutoff counts
interaction labels, and the energy normalization and factor two are essential
qualifications. For an actual nearest-neighbour chain, the support-overlap
graph is derived to be the path graph, and the truncated operator is
factored by its crossing interval component. The two-sided support estimate
and the interval count give operator Schmidt rank at most $r^2q^r$ at every
cut. Actual site-dependent MPO tensors with that uniform bond dimension
are constructed for the same truncated operator. The same MPO satisfies
the displayed normalized error estimate; a rank or decomposition hypothesis
is not supplied by the caller. This does not assert efficient numerical
computation of the tensors.

The first printed uniform energy estimate for soft truncation has
a separate three-qubit counterexample with fixed gap $1/2$, recorded in
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`. This is an exact
mathematical calculation, not a Lean counterexample theorem; its conclusion is
confined to that uniform energy estimate. Independent order and scale are now treated through the exact identity
$h_{m,t}(x)=(t/m)h_{m,m}(mx/t)$. Choosing $t=3m$ preserves the physical
exponential moment and makes every heat parameter at most $1/3$.
The actual finite heat sum has coefficient budget at most $t2^{m+1}$;
approximating its heat terms directly gives an actual interval MPO.
For $\rho=\min(1,w/2,\delta w^2/[2(\eta+2)])$, the choice
$m=\lceil12+2\eta/3+(16/3)\log(80/\rho)\rceil$ precedes all physical
data and gives the same two directed window comparisons and
$0\le E_0-E_s\le\rho$. For every requested MPO error $\xi>0$, an
explicit logarithmic cutoff $\ell$ gives bond dimension
$(1+Nq^2)+(m+1)\ell^2q^\ell$ for this same actual soft Hamiltonian.
The norm error follows from the corrected cluster tail and the heat coefficient
budget. This treats one interval; the full multi-region construction and a
running-time theorem remain open.

The exact formal statements, their source passages, and their verification evidence
are recorded in the blueprint and the dated audit reports. A statement identified as a formalization of a source theorem must carry the
source's hypotheses. A corrected or restricted conclusion is stated separately
and is not counted as the printed theorem.
