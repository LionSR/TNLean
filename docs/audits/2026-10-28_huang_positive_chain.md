# The original positive nearest-neighbor interaction as a chain Hamiltonian

The constructor `ChainHamiltonian.ofNearestNeighborPositive` embeds the original data
$h_i$, indexed by $i\in\operatorname{Fin}(L-1)$, into `ChainHamiltonian L q 1 1`.
Its hypotheses are precisely support on the adjacent-site interval $[i,i+2)$ and the
Loewner inequalities $0\le h_i\le I$. No positivity or nonemptiness assumption on
$L$ or $q$ is added.

This is the adjacent-pair model of
[Landau, Vazirani and Vidick, arXiv:1307.5143v1](https://arxiv.org/pdf/1307.5143v1),
`algo53.tex`, used by the viable-set algorithm, and
[Huang, arXiv:1406.6355v6](https://arxiv.org/pdf/1406.6355v6), Section 5.4,
Lemmas 18–19. It identifies the original operator with the finite-range representation
required by size and bond trimming, without changing the operator used by filtering.

The existing `nearestNeighborChainSupport` is reused. Distinct edges have distinct
supports, because the least site of each interval is its edge index. Each interval has
exactly two sites, including at the final edge. The constructor extends the actual edge
family by zero along this injective map. It therefore assigns the original $h_i$ to
each designated adjacent pair, and zero to all singleton supports. Positivity, the upper
identity bound, Hermiticity and the norm bound one are preserved term by term. The
zero-dimensional matrix case is covered by the existing C*-algebra norm-order theorem.

The theorem `ChainHamiltonian.ofNearestNeighborPositive_operator` proves the exact identity

$$
 \bigl(\operatorname{ofNearestNeighborPositive}(h)\bigr).\operatorname{operator}
 =\sum_{i=0}^{L-2}h_i.
$$

The proof restricts the support sum to the image of the edge-support map and reindexes by
that injection. Thus all spectral and ground-vector hypotheses can be transported by
rewriting this equality; no independent approximation or spectral assumption is introduced.

The actual module `Huang/PositiveChainHamiltonian.lean` passed strict separate-module
compilation with standard linters and warnings treated as errors in 8.91 seconds. Its
SHA-256 is `d719971fdaedf0a5d0a007465927ec08e309b4c813e21887097bc320a63f83c0`.
The manual imported foundation audit checks all nine public declarations and passed in
19.70 seconds, reporting only `propext`, `Classical.choice` and `Quot.sound`. Its temporary
source SHA-256 is `83e6e1ce78276957d54923e2ed6e312ad7830da1016ea9be3a4f508cae2caf2b`.
Manual foundation checks are kept under `/tmp`, with no permanent test fixture. All
compilation outputs are private temporary objects against the agent's existing seeded
dependencies. No Mathlib source is compiled, no shared cache or dependency pin is changed,
and no duplicate ordinary build is started. Ordinary integration and compiled blueprint
declaration checks remain subsequent verification.

Static blueprint synchronization and reverse declaration coverage pass. The chapter passes
the repository LaTeX formatter and ChkTeX configuration; prose, whitespace, proof-integrity
and tactic-pattern checks pass as well.
