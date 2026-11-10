# A physical improving family between buffered low-energy spaces

This contribution addresses the nested-target step in ALVV,
arXiv:1602.08828v2, Theorem 4.8 (`t:aisgapless`, source lines 1027–1041).
It does not establish the full theorem or the sampled binary-tree construction.

For supported positive nearest-neighbour contractions and the stated interior
five-region geometry, the construction chooses actual regional ground energies,
a common clipping threshold, and the original centered ground energy
`0 ≤ E0 ≤ 4`. The same clipped Hamiltonian supplies both one-sided spectral
comparisons and the common polynomial family. At bandwidth `eta` and buffer
`w`, the targets have cutoffs `E0 + eta - 2w` and `E0 + eta - w`.
The original space below `E0 + eta` is epsilon-close to the upper target;
the lower target is epsilon-close to the original space below
`E0 + eta - 3w`. No spectral gap between the targets is assumed.

The polynomial, its exterior factors and the common regional family precede
all viable subspaces. The actual degree is `ell²`, the regional family has
at most `D²` members, with `D = (q ell²)^(20 ell)`, and the retained squared
shrinking estimate is

```
Delta = (2 exp(-2 ell² sqrt(w / (3t + 4ell - (E0 + eta - 2w)))))².
```

Applying the constructed family to an arbitrary delta-viable subspace for
the upper target gives viability `Delta / (1-delta)²` for the lower target
and dimension growth at most the cardinality of the family.
The abstract auxiliary states its polynomial-decomposition input explicitly;
the physical theorem supplies it from the supported Hamiltonian rather than
adding a decomposition or contractivity hypothesis.

The buffer restriction is `3w < eta`. The source hypothesis
`eta1 ≥ 2mu/log n` gives `eta1 ≥ 6w` when `w = mu/(3log n)` and the integer
length satisfies `n ≥ 2`. The length substitution has not been formalized
here. The five-region geometry forces `L ≥ 5`. The cases `n = 0,1` do not
have the positive-log substitution, and lengths 2–4 need a direct construction
outside this geometry. Arbitrary prescribed intervals, boundary regions,
the favorable `D^12 Delta` bound and printed asymptotics, the low-density
bootstrap and the sampled tree remain open. The false soft-cluster estimate
is not used. See `docs/paper-gaps/alvv16_low_energy_family_buffers.tex`.

## Verification provenance

Initial source verification uses the fully compiled common integration
provider at source commit `7881dbe5a91f1436913a0a97d9812b0149aa3165`,
with doc-only successor `8153728de51a3a489c932a8f377690c764892326`, and
immutable QICLean pin `b66600027b2e60ccafea43d041d563cdd00cf05b`.
The new actual module is compiled separately with the package's strict options
and warnings as errors; all new outputs are private temporary files.
The provider, package checkouts and their caches are read-only. These checks
are not an ordinary build against the older manifest in this implementation
tree. The common-dependency ordinary library and blueprint gates remain
pending until integration. No permanent theorem fixture is added.

The strict separate-module check passed in 24.33 seconds with source SHA-256
`80a0b41c170a19f3979ea59ef7dbf9efc2cf4a92e437916849be76147c393c93`,
below the 45-second changed-module budget. Import-aggregator validation and
the proof-pattern scan passed. Blueprint completion marks are withheld
until the ordinary common-dependency checks succeed.

The new paper-gap note compiles to PDF without unresolved references or
overfull boxes. The collection-wide verdict-marker check accepts this new
note but reports the pre-existing malformed marker in
`alvv16_approximation_parameters.tex`; that older file is unchanged.
