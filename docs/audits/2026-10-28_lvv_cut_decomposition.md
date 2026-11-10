# Cut decompositions with simultaneous left-factor rank bounds

The theorem `exists_cutDecomposition_of_operatorSchmidtRank_le` supplies the algebraic
decomposition needed to apply the deterministic viable-set error-reduction theorem to
one global operator. It assumes a simultaneous operator-Schmidt rank bound $R$ for that
operator at all cuts, and constructs at each $i\le L$ a decomposition

$$
 K=\sum_{j=1}^N A_j\otimes B_j,\qquad N\le R.
$$

Every left factor $A_j$, read in `leftConfigOfFin` coordinates on the first $i$ sites,
has operator-Schmidt rank at most $R$ at every internal cut. This is supporting algebra
for [Landau, Vazirani and Vidick, arXiv:1307.5143v1](https://arxiv.org/pdf/1307.5143v1),
`algo53.tex`, Claim `c:errorreduction`, decomposition `e:decomp`, lines 584–591. It asserts
the decomposition and internal rank conclusion, rather than the full error-reduction
claim or its analytic filtering input.

The construction uses a basis of the span of the actual right operator blocks of $K$ at
$i$. Extend the coordinate functionals of this basis to the full right matrix space.
If these extensions are $\varphi_j$ and the basis matrices are $B_j$, define
$A_j(x,x')=\varphi_j(K_{x,x'})$. Basis reconstruction proves the exact product sum;
the number of summands is the actual cut rank, hence at most $R$. Suitable left factors
or an MPO presentation are not additional hypotheses.

For an earlier cut, view the operator on three factors $X,Y,Z$. A shortest decomposition
$K=\sum_aL_a\otimes Y_a$ across $X\mid YZ$ contracts to
$C_\varphi(K)=\sum_aL_a\otimes C_\varphi(Y_a)$ across $X\mid Y$. Thus right contraction
does not increase that rank. The same fixed functionals defining the $A_j$ work at every
earlier cut. Regional three-way coordinates establish this for nested site regions, and
separate configuration bijections transport it exactly to the left-chain coordinates.
There is no extra factor in either the summand count or the earlier rank bound.

The global hypothesis deliberately includes endpoint cuts. Bounds only at internal cuts
do not imply the stated summand count when $L\le1$ and $R=0$: a nonzero scalar operator on
a one-site chain with local dimension one has no internal cuts but needs one product
summand at either endpoint. The all-cuts statement handles this case correctly. The
physical Gaussian theorem already gives an all-cuts bound, so this formulation applies
directly without adding an assumption. Empty configuration spaces and zero ranks are
also included.

All three actual mathematical modules passed separate compilation with strict
changed-module options, standard linters and warnings treated as errors:

| Module | Time | SHA-256 |
|---|---:|---|
| `OperatorRightContraction` | 2.57 s | `52e152d04e2f809cc443533a2862252ad39c6d73ab0fffa252e1aa9f8aaae437` |
| `RegionalRightContraction` | 6.93 s | `0797545155c5d4271b784a221255ef8bf58fafe1a6e416d1b7c97f069bddf137` |
| `ViableSet/CutDecomposition` | 16.50 s | `608e34fd553ab195176a26bdd00ba0f201c6912071593fdf78e684f188c75db8` |

The imported foundation fixture `scripts/lvv_cut_decomposition_regression.lean` checks
all six public declarations. It passed in 3.05 seconds, and each declaration reports only
`propext`, `Classical.choice` and `Quot.sound`. Its SHA-256 is
`ef1aad7d537870abb309e6aae2e9fb11fbd96e8766685fbb3736b98c185cc8f5`.
Compilation outputs are confined to private temporary artifacts against the existing
prebuilt dependencies. No Mathlib source is compiled, no dependency pin is changed, and
no shared cache is modified. Ordinary integration builds and compiled blueprint checks
remain the coordinator's subsequent verification; no duplicate ordinary build is started.

Static blueprint synchronization and reverse declaration coverage pass, as do the
repository LaTeX formatter, ChkTeX, prose and whitespace checks. The changed mathematical
modules contain no proof-integrity blocker; the tactic scans find no repeated pattern.

The first two modules concern generic finite-dimensional algebra and regional quantum
systems and should eventually move upstream to QICLean. The last module depends on the
TNLean left-chain coordinates and belongs here. Existing QICLean operator-block spans,
minimal decomposition and three-way region coordinates are reused. Their private
coordinate-functional construction is exposed here only through the required existence
and contraction-rank statements.
