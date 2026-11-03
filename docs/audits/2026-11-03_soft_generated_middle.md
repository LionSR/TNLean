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

## Verification

The immutable provider is TNLean `88ab31ce57bdbc4bcb65be00055d1db50df4f259` with its own QICLean `e817ea0a8a46440eddc361d41cc46b9e61ba10f4`. Selected unchanged source and object hashes were guarded. All selected importers affected by the earlier shared coordinate promotion were freshly checked; the new principal-compression owner and affected Jordan consumer were also checked in their separate contribution. Only temporary private objects were written; no provider, dependency cache, or Mathlib source was built or modified.

The complete production source passed the default strict checker in 9.116 seconds, with 515 source/object pairs guarded. The separate placement-norm leaf passed in 33.969 seconds; this exceeds the 25-second warning threshold and is retained without a timing-only retry. A preceding complete generic interval-helper check took 89.489 seconds under host contention; it is retained as earlier proof evidence and does not replace the completed-source timing. Diagnostic checks and intermediate errors remain in the private verification record.

The imported foundation audit of both physical theorems and the placement-norm theorem passed in 17.258 seconds. Each depends only on `propext`, `Classical.choice`, and `Quot.sound`. Temporary audit commands were deleted. Canonical ordinary library and compiled blueprint gates remain integration requirements.


The import-aggregator generator, changed-prose check, whitespace check, proof-token check, and tactic-pattern scan completed. The source-only blueprint scan resolves all three new references. Its whole-library result still reports missing companion declarations because this deliberately cache-free source worktree has no dependency checkouts; those pre-existing dependency references must be checked in the canonical integration environment. No cache was initialized to satisfy that scanner.
