# A residual for the two exterior truncations in AKLV

`AKLV/TwoBlockTruncation.lean` constructs the two exterior clippings directly
from positive-contraction nearest-neighbour interactions. It proves an exponential
residual on the actual low spectral space of every partial outer clipping. It is
an auxiliary result towards AKLV, arXiv:1301.1162v1, Theorem 6.1; it does not claim
that theorem's gap preservation or normalized ground-vector comparison.

## Mathematical statement

Let the sites be partitioned at \(0\le l\le r\le L\). The three actual regional
sums are \(A_0,A_1,A_2\). The remaining bonds form
\(J=\{i:i+1\in\{l,r\}\}\), with \(|J|\le2\), and \(Y=\sum_{i\in J}h_i\).
For arbitrary real lower bounds \(e_jI\le A_j\), define

\[
B_T=\sum_{j=0}^2(F_{j,T}-e_jI)+Y,
\qquad
F_{j,T}=
\begin{cases}
\min(A_j,(e_j+t)I),&j\in\{2k:k\in T\},\\
A_j,&\text{otherwise},
\end{cases}
\]

where \(T\subseteq\{0,1\}\). The middle sum is always retained. Spectral calculus
is applied to the actual regional matrices, rather than to supplied exterior
operators. In particular,
\(B_\varnothing=\sum_i h_i-(e_0+e_1+e_2)I\).

Every \(B_T\) is proved Hermitian. Its canonical eigenbasis and actual spectral
subspace \(G_T(\varepsilon)\) below \(\varepsilon\) are then constructed internally.
For \(\varepsilon\ge0\) and \(t\ge\varepsilon+5\), the public theorem gives

\[
\left\|(B_\varnothing-B_{\{0,1\}})|_{G_T(\varepsilon)}\right\|
\le64\exp\left(-\frac{t-\varepsilon}{8}\right)
\]

for every partial clipping \(T\). No spectral basis, residual, perturbation,
closeness estimate, or approximate ground-space projector is a hypothesis.
The scalar lower bounds need not be attained; zero is always allowed.
Coincident cuts, empty outer regions, empty low spaces, and local dimension zero
are included wherever the original matrix formulation permits them.

The proof applies the existing original-bond regional residual theorem with
imaginary time \(1/8\), auxiliary energy \(u=\varepsilon+5\), and at most two
connecting bonds. Each regional error is at most
\(32e^{-(t-\varepsilon)/8}\); summing the two exterior errors gives the stated
constant. The middle and connecting terms cancel exactly in the discrepancy.

## Comparison with the source

The comparison uses [AKLV v1, Sections 6.1 and 6.3](https://arxiv.org/html/1301.1162v1).
The source truncates exactly \(H_L+H_1\) and \(H_s+H_R\), retaining the intervening
interactions. The three-region geometry above gives these two exterior blocks
from the original nearest-neighbour interactions. The shifted raw threshold
\(e_j+t\), followed by subtraction of \(e_jI\), is the spectral clipping of the
centered regional operator at \(t\).

The particular scalar normalizations used by the source, including the argument
that the normalized ground energy is at most six, are not yet constructed in
this module. Nor does the theorem cover arbitrary supplied exterior operators
from the source's more general Hamiltonian formulation. The remaining work is
recorded in `docs/paper-gaps/aklv13_two_block_robustness.tex`. The new blueprint
entry states precisely the proved residual and does not mark Theorem 6.1 as proved.
The ALVV five-region construction clips three bulk sums and is not substituted
for the two exterior clippings.

## Verification

The exact production source has SHA-256
`c1e3980991c988500fdbe00d3672516fa777f7a104557b9662be028a59db6fb1`.
It passes the private separate-module check in 7.48 seconds with strict implicit
arguments, `maxSynthPendingDepth=3`, Mathlib standard linters and warnings as errors.
An imported manual inspection of both definitions and the public theorem passes
in 2.72 seconds. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
All inspection commands and objects remain under `/tmp`; no permanent fixture
is added.

The read-only artifact provider is TNLean
`8153728de51a3a489c932a8f377690c764892326`, with QICLean
`b66600027b2e60ccafea43d041d563cdd00cf05b`.
The sole change from the fully checked mathematical snapshot
`7881dbe5a91f1436913a0a97d9812b0149aa3165` is
`docs/audits/2026-10-28_common_area_law_constructions.md`; no Lean source or dependency
input changed. The checker asserts that provider identity, the companion pin,
and the prebuilt Mathlib sentinel before elaboration. Existing provider artifacts
are exposed by read-only leaf symlinks in a private namespace; new artifacts are
written only under `/tmp`. No patched cache was copied and no dependency source
was rebuilt.

The scoped tactic scan reports no repeated blocks at its default thresholds.
The recurring canonical-eigenvector coordinate conversion is recorded in the
pattern ledger. Reader-facing prose and the source-to-blueprint declaration
check pass for this contribution. Ordinary module verification and compiled
blueprint integration remain pending the common integration tree. The new chapter
should follow `ch35_aklv_chebyshev_filter.tex`; the regional residual chapter must
also be present. Generated aggregators and chapter input registration are excluded
from this contribution.
