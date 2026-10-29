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
$t\ge(1024/g)(E_0/g+1)$ gives an actual truncated gap at least $9g/10$ and a
phase-aligned unit ground vector with squared error at most $e^{-t/16}/100$.
The original gap bound $g\le1$ is derived from the physical hypotheses.
The local support and middle-normalization corrections, and the finite-window
restriction, are recorded in `docs/paper-gaps/aklv13_two_block_robustness.tex`.
The favorable approximate-projector parameter choice, entropy argument, and
approximation sequence remain distinct steps.

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

The global approximation also gives one $r$-dimensional reference space,
mutually $\varepsilon$-close to the full physical ground space, whose every
vector has bond bound $r^2B$. This reference is chosen before the viable space
to be trimmed. It supports collective trimming; it does not supply a sampled
merge construction.

The power-filter application now constructs one actual sample satisfying both
operator-norm approximations, all letter-count bounds, and every spatial Schmidt
rank bound $\ell q^{2u}$. Its explicit sample count retains the ground-energy
factor $\exp(2E_0\log Q/\Delta)$. The same sample is used for the norm and rank
conclusions. This supplies the physical sampling step with its stated cost; it
does not imply a polynomial bound uniform in the unknown ground energy. At a specified
ground energy, the actual sampled operator supplies cut factors chosen before all
input viable families. They improve half-viability to prescribed error with
cardinality and internal bond bounds derived from the same sample. The stated
ground vector currently precedes sampling in this theorem; an assertion with the
family before all ground vectors requires the corresponding quantifier order.

For low-energy targets, one actual clipped Hamiltonian now supplies both buffered
spectral comparisons and a common polynomial improving family. The family and its
tensor factors are selected before the viable subspace, with cardinality at most
$D^2$, where $D=(q\ell^2)^{20\ell}$, and nested-target loss
$\Delta/(1-\delta)^2$ between the clipped targets. Composing the two actual
spectral comparisons gives improvement between the original windows, with loss
$2(\Delta/[1-2(\delta+\varepsilon)]^2+\varepsilon)$ when
$\delta\ge0$ and $2(\delta+\varepsilon)<1$.
The result retains interior geometry and a strict buffer $3w<\eta$. The source parameter bounds, low-density induction, short regions,
and sampled tree still require further arguments. The soft-truncation argument
also requires a correct replacement for the false printed cluster estimate.
Neither the degenerate area law nor a single global MPS approximation supplies
these steps.

The exact formal statements, their source passages, and their verification evidence
are recorded in the blueprint and the dated audit reports. A statement identified as a formalization of a source theorem must carry the
source's hypotheses. A corrected or restricted conclusion is stated separately
and is not counted as the printed theorem.
