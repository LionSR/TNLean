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

The current Hastings development includes a physical approximate factorization and
an entropy conclusion at its stated Lieb–Robinson length. Its quantitative bound
uses the corrected doubling constants, with growth proportional to
$4^{\xi'\log q}$ in place of the printed $2^{\xi'\log q}$. The identification
with the source's full Lieb–Robinson hypothesis and the printed quantitative
constant remain separate questions. The precise qualifications are recorded in
`docs/paper-gaps/hastings07_lemma1_decay_length.tex`,
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
The commuting-gap count includes the documented correction. Combining the
spectral suppression with this same operator, then deriving the required
robustness and entropy conclusions, are distinct steps.

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

The sampling results provide one actual sample with both a matrix-mean error
bound and simultaneous word-frequency bounds whenever the explicit sum of the
two failure bounds is less than one. This is not yet the physical power-filter
application, whose ground-energy dependence must still be retained.

The low-energy construction is a separate problem. Approximation below an energy
cutoff generally permits a slightly larger output cutoff. The corresponding
error-reduction argument therefore involves nested target spaces, not a single
gapped projector. The soft-truncation and merge-tree arguments also require a
correct replacement for the false printed cluster estimate. Neither a degenerate
area law nor a single global MPS approximation supplies these missing steps.

The exact formal statements, their source passages, and their verification evidence
are recorded in the blueprint and the dated audit reports. A statement identified as a formalization of a source theorem must carry the
source's hypotheses. A corrected or restricted conclusion is stated separately
and is not counted as the printed theorem.
