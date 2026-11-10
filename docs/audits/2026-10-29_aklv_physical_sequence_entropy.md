# AKLV entropy from the actual coherent filter sequence

## Physical statement and quantifiers

`exists_aklv_physical_entropy_bound` proves that there is a universal
$C>0$, chosen before the length, local dimension, Hamiltonian, gap,
ground vector and cut, such that, for every $0\le k\le L$,

$$
 S_k(\Omega)\le\frac{C}{g}(1+\log q+\log(1/g))^3.
$$

The physical data are a nearest-neighbour sum $H=\sum_i h_i$ of supported
positive contractions, a unit eigenvector $\Omega$ of energy $\mu$,
the positive rank-one projector gap inequality
$H-\mu I\ge g(I-|\Omega\rangle\langle\Omega|)$, and the actual excited
spectral value $\mu+g$. There is no supplied filter, spectral tail,
rank schedule, fitting window, approximation vector, local-dimension
lower bound or upper-gap bound. The last two bounds are derived from
the original interaction independently of window fit.

The actual-first-excited-energy hypothesis remains explicit. The displayed
inverse-gap logarithms are also retained; no sharper formula with these
logarithms removed is claimed. This is an entropy consequence of the
actual AKLV construction, not a running-time theorem or a complete
formalization of every formulation of the source robustness statement.
The support, regional normalization and index corrections are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.

The source is AKLV, arXiv:1301.1162v1, Lemma `l:5` and the entropy summation,
lines 1003–1075, in the official local file
`/tmp/tnlean-aklv-official-source-20261029/source/1dfrustrated34.tex`
(SHA-256 `65bf824cd7d4f89bef5d819f713ac751445704bb077e81b4af3eb4ce5f2e4065`).
The printed additive rank summary at line 1053 is read as the logarithm
of the multiplicative product, as required by the construction itself.

## The actual rank costs

The physical proof uses the existing literal dependent recursion
`exists_aklv_physical_changing_target_sequence`. Its initial vector and
every later vector retain their actual polynomial, phase, normalized image
and physical regional minima. For the fixed chosen width
$s=\lceil Au^2/g\rceil$, $u=1+\log q+\log(1/g)$, it supplies unit vectors
$\psi_i$ with squared error at most $2^{-i}/16$ and actual cut ranks at
most $R_i=D_0\prod_{j=1}^iF_j$.

The new scalar proof derives, from the selected thresholds and degrees,

$$
 1\le\ell_j\le240s(j+1),\qquad
 \log F_j\le200000(j+1)^2\log D_0.
$$

Indeed $2t_j+s\le2113s(j+1)$ and $1/g\le s$ give the degree bound.
The exponent of the actual sharp rank formula is at most
$96\ell_j\le23040s(j+1)$. Its logarithmic base is at most
$485(j+1)\log(q(s^2+1))$, which is compared directly with
$\log D_0=32(2s+1)\log(q(s^2+1))$.
No second initial-width logarithm estimate is introduced. These coarse
costs are used for the entropy sum only; the separately proved
fourth-root accuracy-dependent MPS rank comparison is unchanged.

Every filter factor is at least two. Hence $R_i$ is nondecreasing and
$R_i\ge2^{i+1}$. For a marginal of finite dimension $N$, the cutoff
$M=N$ covers the full probability family without an infinite limit or
an assumption that the ranks reach the full dimension.

The actual unit approximants give marginal discarded masses at most
$2^{-i}/16$ through the existing homogeneous Schmidt-overlap inequality.
QICLean's finite rank-tail entropy theorem gives

$$
 S_k\le\log R_0+
 \log2\left(1+\sum_{i<N}2^{-i}/16\right)+
 \sum_{i<N}(2^{-i}/16)\log F_{i+1}.
$$

The existing finite quadratic dyadic moment, exposed by companion commit
`39c6ac7a505fa6f363ecb6001e5bfe405b616af9`, bounds the last sum by
$275000\log R_0$. The total is at most $300000\log R_0$.
Its statement and proof are unchanged; no new moment lemma or infinite
summability argument is introduced. The existing initial-scale theorem
then supplies $\log R_0\le C_0(A)u^3/g$.

## Boundary and short-chain cases

At a cut where the fixed initial window fails to fit, its exact centered
geometry implies $\min\{k,L-k\}\le s$. The actual coefficient rank is at
most $q^{\min\{k,L-k\}}$, so the entropy is at most
$\min\{k,L-k\}\log q\le s\log q\le(A+1)u^3/g$.
A single sufficient universal coefficient is therefore
$C=300000C_0(A)+(A+1)$.
This covers endpoint cuts and chains shorter than the initial window.
No smaller truncation window or independent area-law theorem is used.

The existing `aklv_chain_dimension_and_gap_bounds` is exposed from
`SharpPerCutApproximation.lean` with unchanged statement and proof, and
reused here. No second endpoint-unitary or dimension argument is added.
Its existing blueprint parent now also lists this public helper.

## Verification

The three new production modules and the existing module with the exposed
physical helper passed strict actual-name private checks against fully
checked TN mathematical source
`28e38efedb8621056c907c8ad20e1edd24003a20`, documentation-only successor
`7f87bdc8f1b2354be4950ad515dedda7ee9bec96`, and exact QIC package
`ec3434f7d6fbdfc5318dc55934feb9532e239b81`. The companion's modified module
also passed a strict private check. The final provider guard covers 369
selected imported source and ordinary-object pairs; all selected import
roots report zero pending dependencies. Own source and private-object
hashes are guarded separately.

Final strict timings were 9.17 seconds for the actual scalar costs,
4.09 seconds for finite rank-tail entropy summation, 8.93 seconds for the
physical theorem, and 4.23 seconds for the exposed physical helper's
module. The companion module checked in 5.76 seconds. The strict flags
disable automatic implicit arguments, enable Mathlib's standard linters,
and treat warnings as errors. Temporary imported foundation inspection
covers the seven new public TN declarations and the exposed QIC moment
and passed in 3.55 seconds; only `propext`, `Classical.choice`, and `Quot.sound`, or subsets, occur.
No foundation fixture is committed.

The new entropy chapter covers all six new declarations, and the existing
physical chapter covers the newly public helper. The scoped tactic-pattern
scan found a third repeated derivation of a lower bound on $\log2$;
the new proof now reuses Mathlib's existing numerical logarithm theorem
directly, so the repeated block is not copied. The scan reports no repeated
blocks at its default thresholds after this cleanup.

Only own source worktrees and temporary private outputs were written.
No common source, object or cache was edited or copied, no Mathlib source
was built, and no ordinary build was queued. Ordinary builds and compiled
blueprint checks remain integration gates. Aggregators and chapter
registration are excluded; the new chapter belongs after
`ch35_aklv_sharp_mps.tex`.
