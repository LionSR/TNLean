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

Private checks used the fully ordinary-verified TN mathematical snapshot
`8ace1dccea363b9ea3ee1611083fa3d73292f8a7`, whose clean documentation-only
successor is `bc299f74db315cdb8a077e0b678c0eba1f7e0028`, with the exact QIC
package `34cb0c3a24a9cfb8073e1fe7bb1087bc409fb951`. Fresh selected guards
covered 405 imported TN/QIC source and ordinary-object pairs. The import
readiness check reported zero pending dependencies for all six selected
roots. Provider sources and objects were read-only. New objects were
written only to a fresh private namespace under the system temporary
directory; no build artifact was copied and no Mathlib source was built.

All nine actual new production modules passed separate Lean elaboration
with the strict CI flags, including both automatic implicit options disabled,
Mathlib standard linters, and warnings as errors. The final headline module
passed in 5.34 seconds. A separate imported foundation audit inspected all
35 new public declarations; each depends only on the standard foundations
`propext`, `Classical.choice`, and `Quot.sound` (or a subset). The audit was
kept under the system temporary directory and is not a repository fixture.

Ordinary target/full-library and compiled blueprint verification remain
integration gates; these private checks do not replace them. No ordinary
build was queued by this contribution. The new chapter is intended after
`ch35_lvv_successive_construction.tex`; generated aggregators and chapter
registration are deliberately left to integration.

### Checked source hashes

| Production source | SHA-256 |
|---|---|
| `TNLean/Circuit/SiteEmbeddingOrder.lean` | `b5fa82a9469b98c7a4dcff2bfd310ee8f5bbe48acbdcce87bc0de43436dda2b5` |
| `TNLean/Circuit/ProductBasisPenalty.lean` | `c7a6805f6ee0ea6711ced58d93862320700c38d29981bf43a3711b71a7f9d9eb` |
| `TNLean/MPS/AreaLaw/ViableSet/PrefixColumn.lean` | `aa730b760d904cc53a5feba88b200023a3d2ee99aa5713ff9e94804e46b9b8ae` |
| `TNLean/MPS/AreaLaw/ViableSet/PrefixExtraction.lean` | `fbdcbf33a545b8d9f3badd5b2bbdf384dd0cdccb4edbc4024dce925ad4aab205` |
| `TNLean/MPS/AreaLaw/ViableSet/ChainPadding.lean` | `ad65b263686ae392903109ac230f38253c49934dd10a3affc86bfcfc626bd9af` |
| `TNLean/MPS/AreaLaw/ViableSet/ChainPaddingCoordinates.lean` | `e6751d43fbcc670f45162eaffc6625e858e90fbf71fa532db4626735f5c08ab7` |
| `TNLean/MPS/AreaLaw/ViableSet/ChainPaddingGroundState.lean` | `997aff9f9b0dfedc9bb7f1e4b7bf450f2a67d6010a94288591edc8cab7bbcaad` |
| `TNLean/MPS/AreaLaw/ViableSet/PrefixMPS.lean` | `00064f02146030af590b602f2637a3c2a0c5cad4abbc9c286bbb6bac9718d08b` |
| `TNLean/MPS/AreaLaw/ViableSet/SuccessiveAccuracy.lean` | `3a130b520222ab675defbfe4c0ef37f171e48735756a6d5dc8e902ae6fb0ca8e` |

## Completed combined verification

TNLean `da3ab8dcc9` and QICLean `4276de2e` passed full builds, strict
checks, imported foundation audits and compiled blueprint checks. The
complete phase records, timing qualifications and remaining scope are
recorded in [the integration audit](2026-10-29_verified_soft_residual_refinement_range.md).
