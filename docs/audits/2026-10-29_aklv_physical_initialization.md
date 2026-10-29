# The favorable physical AKLV filter and initial vector

The two modules `AKLV/FavorableFilter.lean` and `AKLV/Initialization.lean`
construct the favorable initial filter and its normalized product-vector
output directly from the original nearest-neighbour interactions. This is the
initial step of AKLV's changing-target construction, for a selected window
that fits in the finite chain. It is not the full approximation sequence or
entropy theorem.

## Physical hypotheses and uniform choice

The input consists of positive contractions supported on consecutive pairs of
a chain, a unit vector Ω with ground energy μ, a positive rank-one ground-line
gap g, and the attained excited energy μ+g. The operator inequality is

\[
H-\mu I\ge g(I-|\Omega\rangle\langle\Omega|).
\]

There is no supplied clipped vector, regional minimum, norm ceiling,
perturbation bound, polynomial filter, or operator Schmidt rank estimate.
The two spectral values imply q≥2. The endpoint trial-vector theorem for the
original chain derives g≤1.

One universal constant A≥21 is chosen before chain length, local dimension,
position, interactions, gap and vector. Define

\[
u=1+\log q+\log(1/g),\quad s=\lceil Au^2/g\rceil,\quad
\ell=s^2,\quad t_0=1024+16\log(1/g),\quad R=2t_0+s,
\]
\[
D=\bigl(q(s^2+1)\bigr)^{32(2s+1)},\qquad
\delta=4\exp\left(-4\ell\sqrt{(9g/10)/R}\right).
\]

The available-window hypothesis is a+s+1≤L. The scalar theorem gives s≥21,
Dδ≤10⁻⁵, and the explicit bound

\[
\log D\le198(A+1)(6+2\log(A+1))u^3/g.
\]

The inverse-gap logarithms are retained. No sharper printed asymptotic rate is
claimed beyond this displayed inequality.

## One actual filter and one actual output

The logarithmic robustness theorem chooses the genuine minima of the three
reference regional sums, together with their common unit minimizing vector.
The centered original ground energy E₀ satisfies E₀+Σeⱼ=μ and 0≤E₀≤6.
The actual two-exterior clipped Hamiltonian B has 0≤B, norm at most R, and a
unit ground vector φ with nonnegative energy E and projector gap at least
9g/10. Its phase is aligned so that

\[
\|\phi-\Omega\|^2\le e^{-t_0/16}/100.
\]

A real polynomial p of degree exactly s² satisfies p(E)=1. The actual matrix
K=p(B) fixes φ, preserves φ-perpendicular vectors, has squared shrinking
coefficient δ, and has operator Schmidt rank at most D at the same central
cut a+⌊s/2⌋. These properties follow from the supported shorter-window
polynomial rank theorem and the actual clipped spectral data.

The initial product vector χ is selected for φ. Its overlap satisfies
|⟨φ,χ⟩|≥(2D)⁻¹ᐟ². Applying the checked phase-normalization theorem gives a
unit scalar c and the actual vector

\[
\psi_0=c\,\frac{K\chi}{\|K\chi\|},\qquad K\chi\ne0.
\]

The cut Schmidt rank is at most D. Orthogonal projection gives
\(\|\chi-\langle\phi,\chi\rangle\phi\|\le1\), hence

\[
\|\psi_0-\phi\|^2\le4D\delta\le1/64,
\qquad \|\psi_0-\Omega\|^2\le1/16.
\]

The second inequality uses the triangle inequality after filtering. It does
not transfer the small product-overlap bound from φ to Ω.
The public statement retains the genuine minima, actual B and its ground
vector, polynomial degree and normalization, operator rank bound, actual
product decomposition of χ, and explicit scalar phase.

## Source comparison and remaining scope

The source is [AKLV, arXiv:1301.1162v1](https://arxiv.org/abs/1301.1162v1),
Section 6.1, the initial step in Lemma 6.3. The official local TeX
`1dfrustrated34.tex`, lines 1016–1024, has SHA-256
`65bf824cd7d4f89bef5d819f713ac751445704bb077e81b4af3eb4ce5f2e4065`.

Line 1023 prints the product-overlap inequality with the opposite sign from
Lemma 2.2 and names the original ground vector. The construction applies the
lemma to the actual fixed vector of the clipped filter. This clarification
and the existing regional indexing/count corrections are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.

The available-window restriction is explicit in both new statements and
blueprint entries. The chosen scale guarantees s≥21, hence the existing
six-interaction geometry applies. The full changing-target sequence, its
accumulated rank estimate, finite small-window cases and entropy conclusion
remain separate. Neither new declaration is marked as the entirety of AKLV
Lemma 6.3.

## Verification and exact sources

The actual named modules pass strict private checking with strict implicit
arguments, Mathlib standard linters, warnings as errors and default
heartbeats:

| Module | Source SHA-256 | Seconds |
|---|---|---:|
| `AKLV/FavorableFilter.lean` | `547aef2fce5f777f613d5f5b5ef271a2fea39dfe55795a20274596d39bd8f205` | 6.28 |
| `AKLV/Initialization.lean` | `fa33e877de0c55ec7fd3f889d388078ef821f5b81a18da4f987ccbec4b4fcce1` | 15.50 |

Imported manual foundation inspection of both public theorems passes in
9.26 seconds and reports only `propext`, `Classical.choice` and `Quot.sound`.
The inspection source and output remain under `/tmp`; no permanent fixture
is introduced. Both source hashes and both fresh object hashes are checked
before and after the inspection.

The read-only provider is TNLean mathematical source
`e46d137d7784b6b4abf6155f68d1cb8e6dbc2cd1`, with documentation-only successor
`1604ed2ffc831a4f6afba70150024edd3ca19d6c`. The package pin is QICLean
`afcf986970504f1d370e475f0617256ca83b160d`, whose mathematical source is
`1aa1011b4f5518d59de4ef462b71d84ad4ec33ea`.
A fresh private artifact namespace uses read-only leaf links to ordinary
provider objects. The 293 imported TNLean/QICLean sources and objects, package
manifest and toolchain are guarded before and after checking. The provider,
dependency pins, caches and Mathlib artifacts are unchanged. The source-only
worktree has no `.lake` directory, and no ordinary build is queued here.

The scoped tactic scan finds no repeated blocks at its default thresholds.
The two occurrences of the physical dimension/gap normalization argument are
recorded in the ledger; both already use the shared real-spectrum identity
and endpoint theorem. The two new public declarations have exactly one
blueprint entry each, with valid dependency labels. Full repository source
synchronization in this source-only worktree reports absent dependency
sources; it reports no issue for either new entry. Ordinary module and
compiled-blueprint checks remain with common integration.

Place `ch35_aklv_initialization.tex` after
`ch35_aklv_favorable_parameters.tex`. No generated aggregator, chapter
registration or dependency-pin change is included.

## Completed integration checks

The integrated mathematical revision
`908de62f163b9505312b914a2fad03dafa23948d`, with QICLean pinned to
`01f237e808b03fb0612ceb617f9bca2c407da927`, passed the full 15,106-job
library build and strict checks. The imported foundation audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Source synchronization,
compiled blueprint declaration checks, prose, proof-integrity and timing
checks also passed. No full-build job reached the 25-second warning
threshold. Mathlib was not rebuilt. The complete local check record is
`/tmp/tnlean-moments-initialization-gates.json`.
