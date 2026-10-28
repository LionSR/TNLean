# Simultaneous operator-Schmidt bounds for interval layers

The algebraic bond estimate for one two-layer operator is proved in
`TNLean/MPS/AreaLaw/Huang/BlockProductBonds.lean`. It applies to the disjoint block layers
in [Osborne, arXiv:quant-ph/0508031v2](https://arxiv.org/pdf/quant-ph/0508031v2), Figure 2,
and to the finite propagator sum in
[Huang, arXiv:1406.6355v6](https://arxiv.org/pdf/1406.6355v6), Section 5.4, equation (22).
The analytic approximation of the full propagator is a separate assertion.

For local dimension $q\ge1$, take two fixed ordered lists of operators. Each operator is
supported on its designated interval. Intervals within each list are pairwise disjoint,
with endpoint widths at most $w_0$ and $w_1$, respectively. For the single full-chain operator

$$
 K=\left(\prod_jP_j\right)\left(\prod_jQ_j\right),
$$

the conclusion holds simultaneously at every cut:

$$
 \operatorname{OSR}_k(K)\le q^{2(w_0+w_1)}.
$$

No unitarity, commutation, state, energy or spectral hypothesis is needed. The result
therefore applies to actual block unitaries as a special case. Empty layers and intervals,
zero-width blocks, and repeated empty supports are included.

An interval meeting both sides of the cut after $k$ sites contains site $k$. Thus at most
one interval in a disjoint layer crosses that cut. The existing QICLean theorem
`Entropy.operatorSchmidtRank_cutOperator_list_prod_le` counts the crossing support
occurrences, while one-sided factors contribute at most one. The crossing interval has
at most its endpoint width in sites, giving the layer bound. Submultiplicativity gives
the product bound.

For a finite sample set $J$, the operators may vary with the sample while the support
layouts and orders remain fixed. The same globally defined weighted sum satisfies

$$
 \operatorname{OSR}_k\left(\sum_{t\in J}c_tK_t\right)
 \le |J|q^{2(w_0+w_1)}
$$

at every cut, for arbitrary complex coefficients. Scalar multiplication does not increase
rank, and the rank of a finite sum is subadditive. This includes Gaussian interval masses
and scalar energy-shift phases. Neither a separate approximant at each cut nor a conversion
from Hilbert–Schmidt error is used. These rank statements do not themselves assert an
operator-norm approximation to time evolution or construct its two-layer presentation.

The module passed actual separate-module compilation with the strict changed-module flags
and warnings treated as errors in 12.16 seconds. Its SHA-256 is
`a0069572d8196b123a4a8457206155d4f8cc8a63ccdb6a2022577833ba4a17c1`.
The separate imported fixture `scripts/huang_block_product_bonds_regression.lean` passed
in 10.55 seconds. All five public declarations depend exactly on `propext`,
`Classical.choice` and `Quot.sound`. Source hashes remained unchanged during the checks;
outputs were confined to a private copy of the warmed artifact namespace.

The new chapter uses the common bibliography keys `Osborne2006Dynamics` and
`Huang2015GroundState`. Bibliography entries and chapter input registration are integrated
with the analytic contribution. Ordinary locked module and full-library builds, the
strict imported foundation fixture and compiled blueprint check pass. Completion marks
have been added; see [the integrated verification](2026-10-28_lvv_integrated_verification.md).
