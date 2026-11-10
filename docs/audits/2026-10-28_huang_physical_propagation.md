# Physical two-layer propagation from the original chain interactions

The headline `exists_positive_chain_propagator_approximation` constructs an approximation
to the full physical propagator from the original positive nearest-neighbor contractions.
It takes no partition, supported evolution, tensor representation, spectral assumption or
Lieb–Robinson estimate as an input. The source is
[Osborne, arXiv:quant-ph/0508031v2](https://arxiv.org/pdf/quant-ph/0508031v2), Figure 2 and
equations (2)–(13), as used in
[Huang, arXiv:1406.6355v6](https://arxiv.org/pdf/1406.6355v6), Section 5.4, Lemma 19.

The previously constructed uniform grid fixes each omitted edge index and each internal
edge's block owner. The new Hamiltonian decomposition forms the actual block sums $A_j$
and the signed omitted terms $B_k=-h_{c_k-1}$, and proves $H=A-\sum_kB_k$ with
$A=\sum_jA_j$. Each $A_j$ is supported on its actual block. Disjointness gives commutation
and the exact ordered factorization $e^{itA}=\prod_je^{itA_j}$, with every factor supported
on its block.

The retained original interaction family sets the omitted edges to zero. A direct incidence
count proves that at most two of its designated supports meet any site, giving site norm
budget two. The existing chain Lieb–Robinson theorem therefore derives, for each actual
boundary pair and its radius-$r$ buffer, a projected-generator error

$$
 C e^{v|s|-r/2},\qquad v=8e^2+1,
 \qquad C=\frac{8(2+8e^2)e}{1-e^{-1/2}}.
$$

Applying the constructed disjoint projected paths gives one full-chain operator family
$K(t)$, of two actual disjoint interval layers, with

$$
 \|e^{-itH}-K(t)\|\le\lfloor(L-1)/w\rfloor C|t|e^{v|t|-r/2},
 \qquad \operatorname{OSR}_k(K(t))\le q^{2(w+2r+2)}.
$$

The same operator occurs at every cut; no cut-dependent approximant or conversion between
Hilbert–Schmidt and operator-norm error is used. The final radius is chosen explicitly,
before every sample time, as

$$
 r=\left\lceil2\left(vT+\log\frac{(L+1)C(T+1)}{\min\{\varepsilon,1\}}\right)\right\rceil_+,
 \qquad w=2r+2.
$$

The resulting error is at most $\varepsilon$ simultaneously for $|t|\le T$, and every cut
rank is at most $q^{8r+8}$. A proved width estimate is

$$
 w\le4\bigl((v+1)T+\log(L+1)+|\log C|+
                 \log(1/\min\{\varepsilon,1\})\bigr)+4.
$$

The headline derives Hermiticity and the norm bounds from $0\le h_i\le I$ in the Loewner
order. A separate, stronger theorem permits all Hermitian nearest-neighbor terms of norm
at most one. Empty chains and cutoff zero are included.

The physical construction is split into six modules. All passed actual separate-module
compilation with strict changed-module flags and warnings treated as errors:

| Module | SHA-256 |
|---|---|
| `GridHamiltonian` | `076d729bda4e19cfd36f0232e7cb252ec3748b331f16e692a14abfa1243c3671` |
| `GridEvolution` | `8766e65da523108fdf4c7abf23b1e75faad433c1190ce68c5a443d5229cbc905` |
| `GridLocalization` | `c7c51e7e04d6a5b92aef8e665f1a09352fa415811ec91158904f70b8309fdf88` |
| `GridPropagation` | `ad2b31036da9854ff0d9928d66a55a7180fe3f80507047abfeb19e01f9ce986e` |
| `GridParameters` | `7cff621772e250f42c60e00cd59768bd4b6f001c0c4ecef16c3495b5c1384531` |
| `PhysicalPropagation` | `f122e97fb01302deac706b7f106cf91eaeca3f6b62046458579def2cc121abf1` |

The imported fixture `scripts/huang_physical_propagation_regression.lean` checks all
33 public declarations. It passed in 2.97 seconds, and every declaration depends only on
`propext`, `Classical.choice` and `Quot.sound`. Source hashes remained unchanged during
the checks. Compilation outputs are confined to private temporary artifacts; Mathlib
source was not compiled and dependency caches were unchanged.

The analytic circuit dependency is exactly the independently reviewed
`TNLean/Circuit/DisjointRelativeEvolution.lean`, SHA-256
`5590ed64ff5677934da915d7f72debd5af75cf667670ad0342c40a79f0fe29f3`.
Its unchanged local copy is excluded from this contribution's patch. Ordinary integration
builds and compiled blueprint declaration checks remain required for these six new modules.
No new ordinary build has been started in parallel with the coordinator's verification.

Gaussian quadrature, multiplication by an energy-dependent scalar phase, approximate
ground-energy filtering and viable-set induction are separate steps. In particular, this
propagation contribution makes no claim to complete the unrestricted LVV/Huang algorithm.
