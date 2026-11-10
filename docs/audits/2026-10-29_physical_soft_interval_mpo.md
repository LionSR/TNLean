# One physical soft interval with spectral windows and constructed operator tensors

Date: 29 October 2026.

## The combined result

For positive bandwidth, enlargement and comparison error $\eta,w,\delta$, put

$$\rho=\min\{1,w/2,\delta w^2/(2(\eta+2))\},\qquad
m=\left\lceil12+\frac23\eta+\frac{16}{3}\log(80/\rho)\right\rceil,\qquad t=3m.$$

This order is chosen before every chain length, local dimension, interval and Hamiltonian. For any actual positive unit nearest-neighbour chain on $N+1$ sites and one prescribed interval, the attained regional minima and original ground data are constructed before its approximate regional energy $\epsilon$. The bracket is the source bracket $e_J-10\leq\epsilon\leq e_J$. The exact physical soft replacement is

$$\widetilde H=H-H_J+\epsilon I+h_{m,3m}(H_J-\epsilon I).$$

The actual centered original and soft ground energies satisfy $0\leq E_0-E_s\leq\rho$. The soft window below $E_s+\eta+w$ is $\delta$-close to the original window below $E_0+\eta$, and the original window below $E_0+\eta+w$ is $\delta$-close to the soft window below $E_s+\eta$.

For every $\xi>0$, the same literal $\widetilde H$ has actual site-dependent operator tensors $T$ with $\|\widetilde H-T\|\leq\xi$. Set

$$W=3m2^{m+1},\qquad b=2(e^{1/3}-1)\in(0,1),\qquad
\ell=\max\left\{1,\left\lceil\frac{\log\max\{1,N^2\}-\log\log(1+\xi/W)}{-\log b}\right\rceil\right\}.$$

The tensor dimension is explicitly

$$D=1+Nq^2+(m+1)\ell^2q^\ell.$$

The cluster order depends only on $N,m,\xi$, not on the regional energy, ground vectors, or matrix entries. For each fixed local dimension this is a polynomial dimension budget through the displayed logarithmic order and $W=3m2^{m+1}$. The theorem is an existence and norm statement; no computational running time is claimed.

## Requirement and evidence

| Requirement | Mathematical construction |
|---|---|
| An exact finite expansion, including the constant and scale | The existing scalar soft function equals $\sum_{a=0}^m c_a e^{-ax/t}$ with $c_a=t(-1)^a\sum_{j=1}^m\binom ja/j$. The total absolute budget is at most $t2^{m+1}$. Functional calculus proves the same identity for the same Hermitian matrix. |
| Heat approximants constructed from the physical terms | The existing cluster theorem constructs each heat MPO separately at $a/t$. The actual selected regional terms are the original terms or zero. No supplied approximation family is used. |
| A valid scalar energy shift | For $U=H_J-\epsilon I\geq0$, the actual shift is outside the local terms. The factor $e^{\beta\epsilon}$ is canceled by the proved energy normalization. At the actual minimum $e_J$, the remaining factor is $e^{-\beta(e_J-\epsilon)}\leq1$. |
| A strict decay margin and an actual order | At $t=3m$, every heat time is at most $1/3<\log(3/2)$. The explicit ceiling gives $W(e^{N^2b^\ell}-1)\leq\xi$. |
| Actual tensor closure | Diagonal blocks prove the weighted trace-chain sum, with dimension equal to the sum of the input dimensions. Common-dimension and binary sums reuse this construction. An approximate heat operator is not powered to order $m$. |
| The full Hamiltonian | The exterior local sum and scalar identity are represented exactly at dimension $1+Nq^2$, then added to the regional heat sum. Neither term is omitted from the norm statement. |
| Independent-scale physical residuals | Exact scaling gives $0\leq x-h_{m,t}(x)\leq16e^{x/8-t/16}$ for $m\geq1$, $0<t\leq4m$. The same physically derived exponential moment of $U/8$ therefore controls both windows. |
| The actual reverse cutoff | General soft/hard coercivity retains $t/2-10$ and $\alpha=(t/2)2^{-m}$. At $t=3m$, the order ensures $\alpha\leq3/4$ and $17+\eta+\alpha\leq t/2$. |
| Common ground data and windows | The original and soft minima are identified with the canonical minima using normalized minimizing witnesses. The existing finite-window theorem derives both comparisons from the constructed residuals. |

The combined theorem is `TNLean.MPS.AreaLaw.exists_interval_physical_soft_closeness_and_mpo`. Its hypotheses are the actual local supports and positive unit bounds, interval endpoints, positive bandwidth/enlargement/comparison error, and the source bracket for the chosen regional energy. There is no supplied heat approximation, tensor family, decomposition, cut rank, physical moment, residual, closeness, gap, or ground-space dimension.

## Scope and source

The source is ALVV, arXiv:1602.08828v2, `def:ft` (lines 1152–1157), `def:soft-trunc` (1178–1185), `lem:exp-approx` (1195–1255), and `lem:exp-approx-eff` (1262–1268). The local source `References/1602.08828/local_alg_arxiv_v2.tex` has SHA-256 `19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

This is a corrected one-interval construction at scale three times order. The printed uniform power-based energy estimate and printed physical-support cluster estimate remain false; their counterexamples remain in the two existing paper-gap notes. The new results have their own mathematical blueprint labels, and the false source-labelled estimates are not marked proved. Both notes now describe this bounded corrected consequence.

The independent-scale physical residuals allow any $0<t\leq4m$ and retain the explicit reverse scale condition. The prescribed-accuracy composition specializes to $t=3m$. This is compatible with the short heat times; the old choice $t=m$ was not. The same finite-dimensional exponential moment is used, with no assumption about a reduced-state support. The tensor approximation is to the full exact soft Hamiltonian whose spectral windows are compared; no spectral conclusion about the approximating tensors is added.

Empty and endpoint intervals, a one-site chain ($N=0$), local dimension one, and arbitrary positive $\xi$ are included. The generic block-sum lemma permits empty coefficient families and zero virtual dimensions; absorption of its closing matrix explicitly requires a nonempty physical chain, which $N+1$ supplies. The cluster ceiling is always at least one. The positive soft order makes $W>0$, so the nested logarithm in the budget is defined.

Simultaneous replacements on several prescribed regions, a complete improving polynomial family, and the full algorithm and its running time remain separate tasks. This one-interval theorem is an ingredient for those constructions and is not presented as their completion.

## Reuse and checks

The matrix weighted factorization and reverse scalar cutoff were generalized once; their old public equal-scale versions remain as used specializations. The existing scalar correction bound was made public and reused. The three existing equal-scale physical residual statements are unchanged and their proofs now specialize the independent-scale constructions. The common-dimension and binary operator sums specialize the varying-dimension block theorem. No second soft function, supplied operator oracle, unused compatibility alias, or duplicated matrix spectral calculation is added.

The protected provider is TNLean `7f87bdc8f1b2354be4950ad515dedda7ee9bec96`, with package QICLean `ec3434f7d6fbdfc5318dc55934feb9532e239b81`. The 212 selected source/object pairs, package inputs and the prebuilt Mathlib sentinel are guarded before and after private checks. Temporary objects are selected through explicit imported-artifact entries; no provider artifact is copied or mutated.

All 21 changed proof sources pass the repository strict flags in dependency order; the source-identical existing equal-scale window theorem also passes against the new imported objects. The maximum final source time is 7.72 seconds. A separate imported audit checks all 33 public declarations of these sources and that existing comparison: all use only `propext`, `Classical.choice` and `Quot.sound`. The audit commands remain private and are absent from the patches.

Every new public declaration has a mathematical blueprint reference, and the retained old public declarations keep their existing references. Added labels are unique and all mathematical dependencies resolve. The four-page mathematical addition was rendered twice and visually inspected without overfull boxes or unresolved references. The reader-facing prose check passes and the tactic scan finds no repeated blocks at its default thresholds. No provider source, pin, package, cache, Mathlib source job or ordinary build is changed or started. Complete ordinary integration and common book gates remain pending.
