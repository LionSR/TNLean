# Native middle tensors for the same soft Hamiltonian

The two public results in `ALVV/SoftGeneratedMiddleApproximation.lean` construct the middle approximation from the original nearest-neighbour interaction terms. The first constructs actual native operator tensors and a closing matrix for the raw soft term

    P = p I + h_{m,t}(A − p I).

Here `A` is the actual internal bond sum, `p I ≤ A`, `m ≥ 1`, `t ≥ 3m`, and the requested error is any positive number. No tensor, heat approximation, decomposition, or Schmidt-rank estimate is supplied as a hypothesis. The explicit virtual dimension is twice the sum of the local-sum dimension and the corrected heat-expansion dimension stated in the blueprint.

The construction first masks the bonds outside the interval. It applies the existing corrected heat expansion and takes the Hermitian part. It then restricts these same tensors at the exterior zero configuration, absorbing their ordered exterior products into a closing matrix. Principal compression and placement are contractions. Support of the target follows from support of the actual internal sum and preservation of the supported operator algebra by functional calculus.

The second result retains the exact other four regional terms, all five scalar shifts, and the original crossing bonds. The constructed matrix satisfies `Ghat = G − F 2 + Zphys`, where `F 2` is the raw middle soft term, and its norm error is at most the requested accuracy. In particular, no second soft Hamiltonian or independently selected regional energy is substituted. The hypotheses outside the middle need only the original Hermitian positive-contraction interactions; their scalar shifts are arbitrary real numbers.

Empty native intervals are included: the closing matrix represents their scalar by its trace. The whole chain has `N+1` sites and is nonempty, as required by the global Hermitian-averaging construction. The construction does not infer a general empty-chain periodic representation.

## Source scope

These are operator auxiliaries for ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, `prop:Cheby-AGSP-eff`, and `t:aisefficient`, source lines 1262–1268, 1309–1333, and 1373–1420. The blueprint entries are `lem:native_soft_middle_mpo` and `lem:five_region_soft_middle_mpo`, with exactly the stated hypotheses. They are not marked as the full improving-family or GENERATE theorem.

The corrected interaction-label cluster estimate and energy normalization remain essential. The nondegenerate counterexamples to the printed cluster estimate remain recorded in `docs/paper-gaps/alvv16_cluster_approximation.tex`. This contribution asserts neither the printed spatial selector nor its false bound. It also does not discharge the physical residual and spectral precision conditions at the printed fixed truncation order.

The native tensors may depend on the supplied middle energy estimate. Consequently the existing probability theorem for a family fixed before all adaptive energy choices cannot yet be applied to literal soft GENERATE on this basis alone. Common pre-estimate families or adaptive measurability and probability estimates remain separate requirements. No running-time claim is made.
