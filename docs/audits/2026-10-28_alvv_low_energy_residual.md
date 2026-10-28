# Physical truncation residual for arbitrary low-energy bandwidth

The strengthened declaration is
`TNLean.MPS.AreaLaw.exists_five_region_physical_truncation_residual`.
It concerns ALVV, [arXiv:1602.08828v2](https://arxiv.org/abs/1602.08828v2),
Lemma `lem:hard-trunc`, lines 927–969, and Corollary
`c:goodagsphardtrunc`, lines 979–1005, of `local_alg_arxiv_v2.tex`.
The official TeX source has SHA256
`19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

The Hamiltonian is the original sum of supported positive nearest-neighbour
terms bounded by the identity. The proof constructs the regional minima,
their common product ground vector, and the original centered ground energy
$0\le E_0\le4$. Three bulks are clipped at a real threshold $t\ge21$;
the two retained windows have length controlled independently by $\ell$.
The actual clipped operator has norm at most $3t+4\ell$.

For every current clipping subset $T$ and every bandwidth $\eta\ge0$ with
$19+\eta\le t$, the discrepancy from the final clipped operator, restricted
to the current spectral space below $E_0+\eta$, has norm at most

$$
288e^{11/8}e^{-(t-\eta)/8}.
$$

The earlier statement covered only $\eta\le1$. That restriction is removed:
the proof uses $19+\eta$ as the regional energy-distribution cutoff, so its
actual requirement is $19+\eta\le t$. No spectral gap is assumed. Both
existing ground-space cluster proofs derive the new cutoff inequality
from their previous assumptions, and retain their original statements.

This is a physical low-energy residual estimate, rather than the complete
low-density approximation or area law. One-sided closeness at shifted
cutoffs, the low-energy improving family and the dyadic bootstrap remain
necessary. The independent companion work proves nested-target error
reduction for a supplied tensor decomposition; this contribution does not
change the declared QICLean dependency to that unpublished work.

The selected companion revision remains
`af7e5c90650e5ddb06c2befac508df97fd20b2e3`. The strengthened ordinary source
has passed strict separate-module compilation against prebuilt dependencies
with private output files. Ordinary build and compiled blueprint verification
are recorded separately. No permanent Lean test files are added.
