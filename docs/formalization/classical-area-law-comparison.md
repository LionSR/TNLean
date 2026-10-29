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
| [Hastings, *Solving Gapped Hamiltonians Locally*](https://arxiv.org/abs/cond-mat/0508554) | Gaussian filtering and locality turn Hamiltonian terms into approximately local terms that almost preserve the ground state separately. | A local projective description and generalized MPS approximation; the setting is not confined to a chain. |
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
exponentials are constructed from the interactions. A further construction now
produces the neighbouring-pair family on a regularly blocked physical ring,
from the original Hamiltonian and its unique gapped ground vector. Pair support,
norms and residuals are derived, including the closing pair. The total error is
at most $2N\ell\varepsilon_{\mathrm{loc}}$ on $2N\ell$ sites, with the
actual omitted-shell count retained in $\varepsilon_{\mathrm{loc}}$. The
lower operator bound uses the original ground projector. This first regular
periodic construction does not supply the full hierarchy: the general recursion,
existence of the degenerate-basis refinement, final tensor bond bounds, and thermal
index bound in terms of a local radius remain to be proved. The conditional basis estimates apply to any dimension, but
assume a chosen refinement separating every pair; scalar terminal classes and
refinement existence require an additional argument. This qualification is
recorded in `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`.

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

Several quantitative distinctions must remain visible when comparing the proofs.
The size-trimming estimate uses the library's constant-cut bond bound and corrected
matrix-net exponent. Independent bond trimming requires the documented quadratic
radius. The unrestricted power-sampling estimate cannot be read as a polynomial
bound with a degree independent of the ground energy; the published LVV version
records that dependence. These points are documented in the corresponding
`docs/paper-gaps/lvv13_*.tex` notes.

The ALVV and AKLV constructions use a common companion revision based on
QICLean main `acda92aa`, preserving its matrix Bernstein theorem. The added
low-energy, entropy and interpolation results are compiled together rather than
being assumed from independent dependency revisions.

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
constant. An exact normalization theorem now constructs the phase-aligned output of a
filter with nonzero target overlap, with its residual-to-overlap error and actual
Schmidt-rank growth. The physical favorable filter, product-overlap initialization,
moving-ground-state recursion, and entropy conclusion still need to be assembled.

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
converse estimate holds for every unit vector with constant three. Under a unique
ground-state gap, the squared contraction is $4/(4+\gamma)$ without a gap cap.
Reduction from arbitrary positive contractions to range projections, the regional
truncated Hamiltonian and its spectral and spatial rank conclusions remain open.

The global approximation also gives one $r$-dimensional reference space,
mutually $\varepsilon$-close to the full physical ground space, whose every
vector has bond bound $r^2B$. This reference is chosen before the viable space
to be trimmed. It supports collective trimming; it does not supply a sampled
merge construction.

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
bounds. Choosing the bracket, formalizing the source success probability, and
the complete running-time argument remain separate.

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
it. The sampled tree and a correct replacement for the false printed
soft-cluster estimate also remain open.

The scalar soft truncation is formalized with the corrected cap $t(1+\log m)$,
its polynomial and geometric remainders, and an exponential-weight estimate.
For $m\ge1$, $x\ge0$ and $0<\theta\le1/2$,
$x-h_{m,m}(x)\le(2/\theta)e^{\theta x-\theta m/2}$.
Applying this estimate to a regional Hamiltonian requires a physical exponential
moment bound. The first printed uniform energy estimate for soft truncation has
a separate three-qubit counterexample with fixed gap $1/2$, recorded in
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`. This is an exact
mathematical calculation, not a Lean counterexample theorem; its conclusion is
confined to that uniform energy estimate. A corrected physical spectral comparison
and a sufficient cluster/MPO approximation remain to be proved.

The exact formal statements, their source passages, and their verification evidence
are recorded in the blueprint and the dated audit reports. A statement identified as a formalization of a source theorem must carry the
source's hypotheses. A corrected or restricted conclusion is stated separately
and is not counted as the printed theorem.
