# The coherent successive viable-set construction

The headline `exists_uniform_positive_chain_successive_approximation` constructs one
successive run and extracts a normalized MPS from its actual final span. For fixed
$q\ge2$ and $\Delta>0$, natural $P,d$ are chosen before the length and Hamiltonian.
For each $L\ge1$ and original adjacent-pair positive-contraction interaction, the
entire family sequence is then chosen before any ground energy or ground vector.
The statement has no supplied viable sets, MPS reference, approximate projector,
operator-Schmidt decomposition, propagation approximation or low-energy hypothesis.

For every unit ground vector $\Gamma$ with energy $E_0$ and full-system projector gap
$\Delta$, the same families are viable at every cut, and the final approximation obeys

$$
 \|\psi\|=1,\qquad
 |\langle\psi,\Gamma\rangle|\ge1-\frac{c_\Delta}{L},\qquad
 c_\Delta=(\Delta/169)^2.
$$

The vector is explicitly in the span of the actual final family after the full-left
coordinate isometry, and is an open-boundary MPS of bond dimension at most $P(L+1)^d$.
Every retained family has cardinality and individual effective bond dimension bounded
by this same polynomial.

The source is [Landau, Vazirani and Vidick, arXiv:1307.5143v1](https://arxiv.org/pdf/1307.5143v1),
`algo53.tex`, algorithm steps 1–4 and Claims `c:ext`, `c:2`, `c:trim`,
`c:errorreduction`, lines 379–592, and the final induction at lines 652–678.
Error reduction uses the actual Gaussian construction of
[Huang, arXiv:1406.6355v6](https://arxiv.org/pdf/1406.6355v6), Section 5.4,
Lemmas 18–19. The conclusion states the displayed overlap precision, rather than
arbitrary accuracy. No computational running-time theorem is asserted.

## The physical step

`exists_positive_chain_successive_step` first extends the preceding family by the
one-site basis. The original physical operator is embedded exactly in the finite-range
model through `ChainHamiltonian.ofNearestNeighborPositive`; its singleton terms are
zero and its adjacent-pair terms are the original positive contractions. The actual
polynomial size-trimming family is then constructed, followed by independent trimming
of each retained vector. The finite Gaussian filter family acts on this resulting
half-viable family. The output is selected before every ground pair and restores
viability error $c_\Delta/L$.

Writing $C_sL^p$ for the existing size-trimming cardinality bound, $m_L$ for the corrected
reference trimming radius, and $E_L,R_L$ for the actual filter energy count and rank bound,
the positive-cut budgets are exactly

$$
 s_L=C_sL^pE_LR_L,\qquad b_L=R_L\max\{1,m_L\}.
$$

In particular they are reset at every cut and do not multiply the preceding family size
or bond bound. `SuccessiveBudgets.lean` proves that natural polynomial constants chosen
before $L$ bound $\max\{1,s_L\}$, $\max\{1,b_L\}$ and
$s_L\max\{1,b_L\}$. It uses the independently proved uniform natural filter polynomial
and the existing polynomial bound for the actual reference trimming radius. The maxima
include the scalar initial family without assuming a size coefficient is nonzero for
every arbitrary formal gap parameter.

## One recursive run

`SuccessiveConstruction.lean` uses an actual dependent recursion. A state at $i$ consists
of its finite family together with cardinality, member-MPS and all-ground viability
invariants on the prefix $i\le L$. The initial state is the scalar singleton. A successor
chooses directly from the checked step applied to `previous.val`, using the preceding
state's member-MPS invariant. The viability invariant is then transported from that
same predecessor. The run is `Nat.rec initial advance`; it is not a collection of
independent choices from separate per-cut existence statements. Beyond the finite prefix,
empty families are used without an assertion of viability.

Neither $E_0$ nor $\Gamma$ occurs in a successor choice. Both remain universally quantified
inside the invariant, after the family is chosen. The initial viable witness is the
ground vector itself, which is normalized by the ground-state hypotheses. The final
proof uses exactly this recursively generated $S_L$.

## Extraction and scope

The final right configuration space has one point. The actual normalized viable witness
therefore lies in the span of $S_L$ in full-left coordinates. Pulling back by the coordinate
isometry preserves its norm and overlap. The finite linear-combination/cut-rank bound
gives bond dimension at most $s_L\max\{1,b_L\}$, which is controlled by the already chosen
polynomial. An independent area-law MPS existence theorem is not substituted for this
final extraction. The existing constant-accuracy MPS reference is used only in the actual
bond-trimming estimate, as in the source's reference approximation lemma.

The quantitative scope is explicit. The radius is the corrected quadratic radius recorded
at <https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>. The size coefficient
uses the library constant-cut bond and corrected matrix-net exponent documented in
`docs/paper-gaps/lvv13_constant_bond.tex`. The Gaussian filter replaces the problematic
extensive-energy power-sampling estimate, with the scope documented in
`docs/paper-gaps/lvv13_sampling_ground_energy.tex`. No sharper printed constants or inverse-gap
dependence are claimed. The nondegenerate ground-space setting and $q\ge2$, $L\ge1$ are
visible in the headline signature; no assertion about the ALVV degenerate-ground-space
programme follows from this result.

## Verification

All four actual production modules passed separate compilation with strict changed-module
options, standard linters and warnings treated as errors:

| Module | Time | SHA-256 |
|---|---:|---|
| `SuccessiveBudgets` | 16.19 s | `e85322a267feb76a54dd857339e9b0cefbe1a630dfd5b0bc7147a1725b8c33d1` |
| `SuccessiveStep` | 14.50 s | `68e7271a0832d925c255319fbc5bd1985c8b3a1d15ce18a6bd0bf25559160e3e` |
| `SuccessiveConstruction` | 27.68 s | `1bd1bc3da44ab99218449d525bc5c6508a6353a11c5d868216c6cbec10505064` |
| `SuccessiveApproximation` | 17.24 s | `000e119c1ce66a151b666ca807585a1612e1cc6fd729fcc602153d7e90cf5b97` |

The recursive module's wall time is above the 25-second warning threshold and below the
50-second failure threshold. The checked sources remained unchanged. The manual foundation
audit imports the actual final module and checks all ten new public declarations. It passed
in 17.72 seconds and reported only `propext`, `Classical.choice` and `Quot.sound`. Its temporary
source SHA-256 is `0858629a10d3caebb4bd515f7bf64e626c56d6736633124742e7a97c728998ec`.
No permanent Lean test fixture is added.

The independently reviewed physical filter dependencies were copied unchanged into this
isolated worktree and checked as actual separate modules. Their final physical-family and
viable-filter hashes are respectively
`a0b5ef5ec57f8d568b436ca895e7121e191d28589c8261fcbd9aaa61dbf5a50a` and
`a3e8b6aafedee3a3f25979b4c43da27b3e4ce67193ed5f06b85aa0d3eaf0f117`.
The ordinary guarded dependency build also completed successfully with 4,014 jobs, including
the physical-family and viable-filter modules in 15 and 4 seconds respectively, as recorded
in `/tmp/tnlean-physical-viable-filter-ordinary.log`.
These copied dependencies, generated aggregators and chapter input registration are excluded
from this contribution's patch.

All compilation outputs are private temporary objects against the agent's already seeded
worktree. No Mathlib source is compiled, no shared cache or dependency pin is modified, and
no ordinary build is started alongside the coordinator's frozen verification. Ordinary
integration builds and compiled blueprint declaration checks for these four new modules
remain subsequent verification.

Static blueprint synchronization reports 30,220 declaration references with no missing,
stale or duplicate references. Reverse coverage includes all ten new public declarations.
The chapter passes the repository LaTeX formatter and ChkTeX configuration. Prose,
whitespace, proof-integrity and tactic-pattern checks pass. The recursive construction
and its actual-final-span extraction also received an independent read-only review;
no material issue was found.


The contribution was subsequently applied to the current-main integration worktree.
The guarded ordinary target passed 4172 jobs, including all four new mathematical
modules. Their reported build times were 10, 3.5, 3.5 and 3.7 seconds. The same target
also verified the general-probability integral trace-exponential bounds. Full-library,
strict imported-source and compiled blueprint checks are recorded separately for the
resulting integration revision.


The combined mathematical snapshot `fea97ebd91cb1858b670892eadbb8d5028c46b7b`
subsequently passed the full library build (15013 jobs), strict checks of all 11
changed source files, manual ordinary-object inspection of its 24 new public
declarations and compiled blueprint declaration checking. The inspected declarations
use only `propext`, `Classical.choice` and `Quot.sound`. The full build contained no
Mathlib source-compilation jobs. No permanent Lean fixture was added.
