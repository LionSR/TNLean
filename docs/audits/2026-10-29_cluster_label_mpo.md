# A constructed matrix product operator for the corrected cluster truncation

Date: 29 October 2026.

Let $h_i$, $0\leq i<N$, be operators on $N+1$ sites of local dimension $q\geq1$, each supported on the designated pair $\{i,i+1\}$. Let $r\geq1$. The existing interaction-label truncation $M_r$ has operator Schmidt rank at most $r^2q^r$ across every chain cut. There are actual site-dependent matrices $A_v^{s,t}$ of size $r^2q^r$ such that

$$ (M_r)_{\sigma,\tau}=\operatorname{tr}\left(A_0^{\sigma_0,\tau_0}\cdots A_N^{\sigma_N,\tau_N}\right). $$

The representation theorem requires neither Hermiticity nor positivity. If the interactions are Hermitian with operator norm at most one, $H=\sum_i h_i\geq\lambda I$, $\beta\geq0$ and $b=2(e^\beta-1)\leq1$, the same represented operator satisfies

$$ e^{\beta\lambda}\|e^{-\beta H}-M_r\|\leq e^{N^2b^r}-1. $$

## Construction and bounds

The exact physical crossing decomposition and all its side factors were constructed in the preceding eight-module contribution. No decomposition is supplied to the physical rank theorem. A connected interval $C$ of labels has designated physical support of cardinality at most $|C|+1$. If $|C|<r$, this support has at most $r$ sites.

For an operator supported on $X$, the two support-square estimates give

$$\operatorname{OSR}_A(T)\leq\min\{q^{2|X\cap A|},q^{2|X\setminus A|}\}\leq q^{|X|}.$$

These bounds are proved in QICLean from the existing left-side support estimate. Exchanging the tensor factors transposes the realigned matrix, so complementary cut ranks agree. No state, positivity, normalization or spectral assumption occurs in these generic statements.

At the cut after site $p$, every retained crossing label interval $C=[a,b]$ contains $p$ and has $|C|<r$. The map $C\mapsto(p-a,b-p)$ is injective, and each coordinate is smaller than $r-1$. There are therefore at most $(r-1)^2$ such intervals. In the actual crossing decomposition, the no-crossing product has rank at most one, and every crossing term has rank at most $q^r$; its two exterior factors are supported on opposite sides and have rank at most one. The sum has rank at most $1+(r-1)^2q^r\leq r^2q^r$.

The all-cut theorem treats the endpoint cuts directly by the one-dimensional configuration space on one side. It also treats $q=1$ and $r=1$ directly. For $r=1$ the crossing family is empty; for $N=0$ the physical chain still has one site, and there are no interior cuts.

Pairing the two physical indices at each site identifies the coefficient cut rank of a vector with the operator Schmidt rank. This equality is proved by explicit separate row and column reindexings. The existing open-boundary MPS construction supplies actual rectangular tensors. Padding and multiplying the scalar cap into the first tensor gives the displayed trace representation with closing identity. The generic constructor explicitly requires a nonempty chain and a positive virtual dimension; the physical application derives these from $L=N+1$ and $D=r^2q^r$.

## Source and scope

The source passages are ALVV, arXiv:1602.08828v2, `thm:cluster` (lines 1298–1303), `eq:rho-expansion` (lines 1971–2013), and the operator construction (lines 2014–2115). The local paper `References/1602.08828/local_alg_arxiv_v2.tex` has SHA-256 `19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

This is a corrected interaction-label theorem. Its selector is the existing cutoff on connected label components, rather than the minimal physical support of a word product. A component of $s$ labels is designated on $s+1$ sites. The approximation is normalized by a supplied lower energy. The original physical-support approximation remains false, as documented in `docs/paper-gaps/alvv16_cluster_approximation.tex`; its counterexamples remain unchanged. Each restricted mathematical statement has its own blueprint label, and the source-labelled false estimate is not marked proved by this contribution.

The proof uses the exact finite Möbius cluster coefficients and the previously proved crossing identity. It does not rely on the printed preprocessing recurrence that omits the empty contribution under the exact-label reading. The represented finite operator is constructed, but no computational running-time bound is asserted.

## Ownership and verification

The four generic factor-exchange, complementary-cut and two-sided-support declarations belong in QICLean. Their two source-file changes form a separate QICLean patch. The six new TNLean sources contain the actual interval support/count, all-cut estimate, paired-site construction, and physical represented approximation. No unused wrapper or duplicate pairing equivalence is added.

The protected provider is TNLean `f93bc77b3dddcc292125eea18b96af153225251b` with package QICLean `4276de2eeb5c4122f4482ef5e4fa205be5b71bd9`. Selected provider source/object hashes, package inputs, the prebuilt Mathlib sentinel, and the complete frozen eight-module prerequisite manifest are checked before and after private elaborations. Existing prerequisite objects are read through explicit imported-artifact entries; none is copied or mutated.

Both modified QICLean sources and all six new TNLean sources pass the repository strict flags in dependency order. The final complete run takes at most 3.83 seconds per source. A separate imported audit checks all fourteen new public declarations, each depending only on `propext`, `Classical.choice`, and `Quot.sound`. Its commands remain in the private evidence directory and are absent from both proposed production patches.

Every public declaration has a mathematical blueprint reference. Added mathematical dependencies resolve, the reader-facing prose check passes, and the tactic-pattern scan finds no repeated block at its default thresholds. The two-page mathematical addition is rendered twice and visually inspected, with no overfull boxes or unresolved references. No provider source, pin, build object, dependency cache or Mathlib source job is changed or started. The ordinary common integration and complete book gates remain pending.
