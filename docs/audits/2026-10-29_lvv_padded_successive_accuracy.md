# Arbitrary accuracy from one padded LVV successive construction

## Mathematical result

For every local dimension $q\ge2$ and positive original projector-gap lower
bound $\Delta$, the theorem
`exists_uniform_positive_chain_successive_accuracy` chooses natural numbers
$P,d$, with $P\ge1$, before the original length $L$, the requested inverse
accuracy $R$, and the positive nearest-neighbour interaction.
For natural $L,R\ge1$, it forms the actual padded chain of length
$N=L+2R^2$ and runs the proved successive viable-set construction once on
that interaction, at the fixed lower gap $g=\min\{\Delta,1\}$.

The padded interaction embeds every original term in the first $L$ sites.
Each appended site carries the actual penalty $I-|0\rangle\langle0|$,
assigned to the new nearest-neighbour bond having that site as right
endpoint. Every term remains a supported positive contraction. The actual
Hamiltonian is $H\otimes I+I\otimes A$, where $A$ is the sum of these
penalties. Its prescribed product basis vector has energy zero and
projector gap at least one. Thus an original normalized ground vector
$\Gamma$ extends to a normalized ground vector
$\widehat\Gamma=\Gamma\otimes|0\rangle^{\otimes(N-L)}$ at the same energy,
with projector gap at least $g$. No equality of attained spectral gaps is
required.

The successive families $S_i$ are selected before the original ground
energy and vector. They are the families of that same padded run, beginning
with the scalar family $S_0=\{1\}$; they are not chosen independently at
each stage. Every retained family has cardinality and individual effective
bond bound at most $P(N+1)^d$. All stages are $c/N$-viable for the padded
target, where $c=(g/169)^2<1$.

At stage $L$, the all-zero right column of the actual viable witness lies
in the actual span of $S_L$ and has norm at most one. Its nonzero overlap
allows normalization, which improves the overlap. A phase rotation preserves
that retained span. In original-chain coordinates it gives a unit MPS
$\psi$ with
$\|\psi-\Gamma\|^2\le 2c/N\le R^{-2}$ and bond bound
$P(N+1)^d$.

The uniform polynomial of the previous successive theorem is squared:
$P=P_0^2$, $d=2d_0$. Consequently its degree is independent of $R$; the
final bound is polynomial jointly in $L$ and $R$. Reducing the gap as a
function of accuracy is not used.

## Source and scope

This product-ancilla argument is a consequence of the proved LVV successive
construction. It is not presented as a printed padding step in LVV13
(arXiv:1307.5143v1, `algo53.tex`, final induction, lines 652–678).
The mathematical construction uses the existing independent-column bond
trimming and Huang Gaussian error reduction. Their documented constant
corrections and conservative bounds remain in force:

- [Quadratic trimming radius](https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf).
- `docs/paper-gaps/lvv13_constant_bond.tex`.
- `docs/paper-gaps/lvv13_sampling_ground_energy.tex`.

The theorem concerns finite families, retained spans, and MPS ranks.
It makes no computational running-time claim or claim to every printed
quantitative estimate. Its hypotheses are the original supported positive
nearest-neighbour contractions, local dimension $q\ge2$, and the
rank-one projector-gap ground-state condition. No supplied ancillary gap,
cut decomposition, viable witness, MPS approximation, or attained excited
energy is assumed.

## Verification

The construction is extracted onto TNLean `6da5dd6c42`, with QICLean pinned
to public revision `648432e86018a50272372ecf2e80c8263e81b601`
([QICLean #1002](https://github.com/LionSR/QICLean/pull/1002)).
The extracted sources contain no `sorry`, `admit`, `native_decide`,
`unsafeCast` or new axiom declarations.

Generated import completeness and the production-file length check pass.
The proof-pattern scan was run; the functional-calculus pattern is recorded
in the ledger, and the uniform bond estimates reuse `IsOpenMPS.mono`.
All newly introduced blueprint labels and citations resolve. The role check
reports only the four existing mismatches in the base revision's
`ch35_aklv_energy_truncation.tex`. The ground-energy note compiles with its
bibliography without unresolved references or layout warnings.

The integrated mathematical development previously passed a full Lake build,
strict checks of the successive-construction modules, and blueprint
declaration checks. Fresh compiled checks of this extracted branch are
reported in the pull request.
