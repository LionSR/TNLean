# Corrected normalized cluster tail on the label path

Date: 29 October 2026.

## Mathematical statement

Let $H=\sum_{i=0}^{N-1}h_i$ be a finite sum of Hermitian complex matrices, each of Euclidean operator norm at most one. Suppose $H\geq\lambda I$, $r\geq1$, $\beta\geq0$, and $b=2(e^\beta-1)\leq1$. For the existing selected word expansion that discards a label support exactly when one of its path components has at least $r$ labels, the proved estimate is

$$e^{\beta\lambda}\|e^{-\beta H}-M_r\|\leq\exp(N^2b^r)-1.$$

The supplied number $\lambda$ is any lower energy. Individual terms may be negative, and no commutation between terms is assumed for this operator norm estimate. The theorem imposes no nonemptiness condition on the chain or matrix index. If the chain is empty or the cutoff exceeds its length, there is no discarded support.

## Requirements and evidence

| Requirement | Evidence |
|---|---|
| Use the existing expansion and cluster parts | The exact finite identities use `clusterOp`, `clusterPart`, and `truncatedExp`; no parallel cluster operator is introduced. |
| Prove the actual discarded event | `noLargeCluster_pathGraph_iff` identifies the actual graph selector with containing a constructed length-$r$ interval. |
| Construct the windows and their labels | `pathWindows`, interval extraction and `pathWindows_exists_marker` use the actual order on `Fin N`; left endpoints give an injective marker. |
| Bound signed coefficients | The proof calls QICLean’s `Finset.norm_sum_powerset_biUnion_sign_le_two_pow` on those actual markers. |
| Prove the normalized analytic bound | The proof calls the checked existing mandatory-label estimate through `norm_clusterPart_empty_boundary_le_of_lower_bound`. Hermiticity of the actual total is derived from the terms. |
| Count actual unions and components | `clusters_biUnion_pathWindows_subset`, `biUnion_clusters`, and `pairwise_clusters` establish the component injection and the product of weights. The interval count is derived from endpoint pairs. |
| Derive the tail without an assumed spatial inequality | `sum_pow_card_unions_pathWindows_le` combines the injection, finite powerset product, $1+x\leq e^x$, and the proved $N^2$ interval count. |

## Source comparison and remaining scope

The reference is ALVV, arXiv:1602.08828v2, `thm:cluster-approx`, lines 1270–1291 and its proof at lines 1935–1968 in `References/1602.08828/local_alg_arxiv_v2.tex`. Its SHA-256 is `19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

The printed estimate remains false under its stated hypotheses. The corrected theorem changes the normalization, uses interaction-label components, and includes the factor two from the grouped coefficients. It is stated under its own blueprint label. The existing two-site and negative-term counterexamples are retained, and the paper-gap note records the proved correction separately. The exact matrix product representation, its cut ranks and bond dimensions, and propagation through the later polynomial approximation are not consequences asserted by this contribution.

## Verification

- Protected provider: TNLean `bc299f74db315cdb8a077e0b678c0eba1f7e0028`, QICLean package `34cb0c3a24a9cfb8073e1fe7bb1087bc409fb951`. All 36 selected imported TNLean/QICLean source and object pairs, package inputs and the prebuilt Mathlib sentinel remained unchanged around private checks.
- All four actual new modules passed the repository strict Lean flags in dependency order. Maximum measured time was 16.42 seconds. Each check read production dependencies and wrote objects only below `/tmp`.
- A separate file imported the final actual module through explicit private `importArts` and checked all sixteen public declarations. Every declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. The audit commands remain under `/tmp` and are absent from the proposed production sources.
- Reader-facing prose and the tactic-pattern scan passed. The generated aggregator was computed by the repository generator against the extended source inventory. The new blueprint section and updated paper-gap note were rendered, their references resolved, and their pages inspected. No overfull boxes remain.
- No provider source, package pin, build object or dependency cache was changed. No Mathlib source job was run. The ordinary integration build, complete blueprint declaration check and common gates remain to be run by the integrating worktree.

## Reused mathematical interfaces

`Finset.indicator_biUnion_eq_sum_powerset`, `Finset.sum_fiberwise_of_maps_to`, `Set.OrdConnected.apply_covBy_apply_iff`, `SimpleGraph.hasse_preconnected_of_succ`, `Fin.card_Icc`, `Finset.sum_le_sum_of_injOn`, `Finset.prod_pow_eq_pow_sum`, and `Finset.prod_one_add` provide the finite sum, graph, order and product arguments. The existing cluster partition is retained.

## Independent review

An independent reading of the final norm and weight proofs checked the explicit lower energy,
actual Hamiltonian sum, actual path and cutoff, component reconstruction, decreasing weights,
and the cases of zero inverse temperature, an empty chain and a cutoff longer than the chain.
No additional geometric event or factorization is supplied in the headline theorem. The
review found no material mathematical defect. The original counterexamples are retained.

## Completed combined verification

TNLean `da3ab8dcc9` and QICLean `4276de2e` passed full builds, strict
checks, imported foundation audits and compiled blueprint checks. The
complete phase records, timing qualifications and remaining scope are
recorded in [the integration audit](2026-10-29_verified_soft_residual_refinement_range.md).
