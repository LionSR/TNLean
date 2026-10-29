# Actual physical crossing-component factorization of the label truncation

Date: 29 October 2026.

## Statement and construction

Let $h_i$, $i\in\{0,\ldots,N-1\}$, be complex operators on $N+1$ sites with designated supports $\{i,i+1\}$. Fix a label $p$ and a real $\beta$. For the existing exact-label coefficients $E_A$, put

$$F(B)=\sum_{A\subseteq B,\,\text{every label component of }A\text{ has size}<r}E_A.$$

The actual corrected label truncation satisfies

$$M_r=F(\{j:j<p\})F(\{j:p<j\})+
 \sum_{C\ni p,\ C\text{ connected},\ |C|<r}
 E_C\bigl(F(L(C))F(R(C))\bigr),$$

where $L(C)=\{j:\forall c\in C,\ j+1<c\}$ and $R(C)=\{j:\forall c\in C,\ c+1<j\}$. All four kinds of side factors are actual finite retained-support sums. There is no assumed successful decomposition, commutation family, spectral gap, positivity, energy or state. In fact, Hermiticity is unnecessary for this identity, so it applies in particular to arbitrary Hermitian interactions. The parameter $r$ is unrestricted in the exact algebraic theorem; for the cutoff interpretation one takes $r\geq1$.

The support of $F(B)$ lies in the union of the designated supports of the allowed labels. More precisely, if $a\leq i$ and $i+1<b$ for every $i\in B$, then $F(B)$ is supported on the physical interval $[a,b)$. Labels $i<p$ therefore give a left-sided operator at the cut after physical site $p$, and labels $p<i$ give a right-sided operator. These statements apply to the constructed exterior factors because $p\in C$.

## Requirement and evidence

| Requirement | Proved evidence |
|---|---|
| Use the actual physical nearest-neighbour graph | `overlapGraph_nearestNeighbor_eq_pathGraph` proves that the overlap graph of the actual designated pairs is the label path. |
| Derive nonadjacent commutation | `commute_nearestNeighbor_of_not_adj` derives it from the designated supports through the supported-operator algebra. It is absent as a hypothesis from the physical headline. |
| Select the actual crossing component | `sum_retained_clusterOp_containing_eq` chooses the component containing $p$ using the existing existence theorem and proves uniqueness through cluster intersection. |
| Prove both directions of the finite correspondence | The proof gives inverse maps $A\mapsto(C,A\setminus C)$ and $(C,B)\mapsto C\cup B$, with the actual residual labels outside $C\cup\partial C$. |
| Construct both exterior factors | `pathGraph_exterior_eq_sides` and `sum_retained_clusterOp_union_eq_mul` identify and factor the actual two sides; the finite supports and sums are not supplied. |
| Include the no-crossing family | The complement of $\{p\}$ is split into its two separated strict order sides, and the same retained-sum product theorem is applied. |
| Derive physical support | `isSupportedOn_sum_retained_clusterOp` proves support termwise from `clusterOp_mem_supportedOperators`; the nearest-neighbour interval and one-sided corollaries derive the actual geometric bounds. |

## Source, cutoff and recurrence

The source passage is ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, in `References/1602.08828/local_alg_arxiv_v2.tex`, lines 1971–2013. Its SHA-256 is `19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

The truncation here counts interaction-label components, not the minimal physical support of a word product. A component of $s$ nearest-neighbour labels is designated on $s+1$ physical sites; smaller actual support is allowed. The result has its own blueprint label and explicit module markers referencing `docs/paper-gaps/alvv16_cluster_approximation.tex`. It does not establish the printed physical-support approximation, and the existing counterexamples remain untouched. The already proved energy-normalized norm estimate is unchanged.

The proof uses the existing exact finite Möbius definition of `clusterOp`, its disjoint-union factorization, and the existing convergent-series identity for `truncatedExp`. It does not use the printed preprocessing recurrence that subtracts only segment families of size at least two. Under the exact-support reading, a single full-support bond already has coefficient $e^{-\beta h_i}-I$, so an empty contribution is required. No claim about that printed recurrence is needed as a proof hypothesis or intermediate result here.

When $r=1$, a crossing component would contain $p$ and have cardinality less than one, which is impossible; the crossing sum is empty. For $N=0$ there is no label $p$ and no interior site cut. The one-site chain and endpoint cuts are therefore separate trivial cases for the later all-cut rank theorem. The current statements allow zero local dimension and empty physical configuration spaces.

## Verification and provenance

- Protected source: TNLean `f93bc77b3dddcc292125eea18b96af153225251b`, QICLean package `4276de2eeb5c4122f4482ef5e4fa205be5b71bd9`. The 88 selected TNLean/QICLean source-object pairs, package inputs and prebuilt Mathlib sentinel were guarded before and after private checks.
- Eight actual new modules passed the repository strict Lean flags in dependency order, with no warnings. The maximum final measured time was 6.75 seconds. The complete timing map and output log remain in the private evidence directory.
- A separate file imported the final actual module through explicit private `importArts` and checked every new public declaration. All eighteen depend only on `propext`, `Classical.choice` and `Quot.sound`. The audit commands remain under `/tmp` and are absent from the proposed production sources.
- The reader-facing prose and tactic-pattern scans passed. The aggregator was computed by the existing generator against the extended source inventory. Every new public declaration has a blueprint reference; the new labels are distinct. The mathematical addition was rendered twice, its references resolved and its pages visually inspected; no overfull boxes remain.
- All new objects and temporary files were written below `/tmp`. No provider source, pin, package, build object or dependency cache was mutated or copied. No Mathlib source job or ordinary build was run.
- The ordinary integration build and complete common blueprint/foundation gates remain pending in the integrating worktree.

## Remaining work

The actual crossing-interval Schmidt-rank count and site-dependent matrix product operator construction are not asserted here. The next steps are to bound the physical support of each crossing interval by $|C|+1\leq r$, derive its two-sided operator Schmidt bound, count the possible crossing intervals, and apply the existing paired-index open-chain construction. The generic separated-component results are explicitly auxiliary; the physical headline discharges their commutation requirement from actual nearest-neighbour supports.
