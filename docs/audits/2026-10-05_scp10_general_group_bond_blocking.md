# General-group physical bond separation

Source: [SCP10, local lines 1818–1915](https://github.com/LionSR/TNLean/blob/3e16cc3db55b962fdc68ebd93cbf2a696339fd0d/Papers/1001.3807/paper_v3.tex#L1818-L1915), Observations 6.5–6.6; tracker [#8676](https://github.com/LionSR/TNLean/issues/8676).
The actual `renorm-gg-sym`, `renorm-g-id-and-split`, and `renorm-fixedpoint` figures were rendered and inspected before implementation.

## Exact result

`RegularGraphBondBlocking.lean` proves a global physical state identity for canonical averaging sites, not merely conjugacy of virtual representations. For a finite group G, finite surplus set K, and finite simple graph Γ, put X = G × (K → G). The local representation translates every X coordinate by the same group element. Each vertex has its actual normalized group-averaging tensor, and the graph state is the genuine sum over one virtual X label per edge.

The explicit physical basis permutation applies (a, b) ↦ (a, a⁻¹b) on every incident physical half-edge. The result is exactly the single-regular-bond averaging-site state times independent endpoint equality vectors. The graph contraction and its |G|⁻|V| normalization are inherited from `graphBondRegrouping_averagingSite_coherent`; the equality is derived by splitting its actual bond factors. No global factorization, block Gram identity, state equivalence, or desired equality is a hypothesis.

Main declarations:

- `regularGraphBlockingIsometry`: full-domain physical linear isometry equivalence
- `regularGraphBlockingIsometry_apply`: its coefficient operation is exactly `regularGraphBlocking`
- `regularGraphBlocking_averagingSite`: exact unnormalized factorization
- `regularGraphBlocking_dotProduct`: every physical overlap is preserved
- `regularGraphResidualBell_eq_prod`: each surplus bond contributes its own equality vector
- `regularGraphResidualBell_dotProduct`: raw Bell-product squared norm is D^|E|, D = |G^K|
- `regularGraphNormalizedBell_dotProduct`: normalized residual product has norm one
- `regularGraphNormalizedBell_eq_prod_omegaVec`: literal identification with standard normalized maximally entangled vectors
- `regularGraphBlocking_averagingSite_normalized`: exact normalized factorization with scalar (√D)^|E|

The local operation reuses `RegularRepresentation.blockingFamilyEquiv`. Its global action is a product of vertex-local permutations followed by a regrouping of physical tensor factors. The isometry is not just attached abstractly: its coordinate formula is identified with the operator used in the state theorem.

## Scope and exclusions

- Arbitrary finite G, including nonabelian groups
- Arbitrary finite simple Γ, including disconnected/empty graphs and isolated vertices
- Arbitrary finite K, including empty K; one uniform surplus set on all edges
- Canonical averaging sites only. Arbitrary given physical G-isometric site tensors have not yet been transported into these coordinates. No extra ambient-surjectivity premise is smuggled in; the next task is the derived physical-support isometry composition from Observation 6.4.
- No actual 2×2 lattice blocking, periodic-seam identification, general inserted closure sector, or independently varying edge-bundle size theorem is claimed.

Consequently this is the actual-network bond-separation step of Observation 6.5, not completion of full Observation 6.6. The new paper-gap note spells out the physical-support and geometric composition still needed. The new blueprint fragment states exactly the canonical theorem and marks no unrestricted source label complete.

## Validation

An isolated output overlay reused the independently audited `peps-completion-validation` dependency baseline. All 89 pre-existing TNLean sources in the new module's 90-module TNLean closure match that donor exactly. `RegularRepresentationBlocking` was compiled privately because its artifact was not in that donor. Two newly needed QICLean artifacts, `Channel.TensorMap` and `Channel.MaximallyEntangled`, were reused only after source comparison with exact pinned QICLean revision `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`. No Mathlib source rebuild, shared artifact mutation, or dependency change occurred.

Checks passed with `autoImplicit=false`, `relaxedAutoImplicit=false`, `pp.unicode.fun=true`, `maxSynthPendingDepth=3`, `linter.mathlibStandardSet=true`, and `warningAsError=true`:

- Production module: 4.66 seconds
- Regression: 2.44 seconds
- All 15 blueprint declaration references checked by Lean against the compiled module
- Four guarded axiom reports: standard `[propext, Classical.choice, Quot.sound]` only
- Generic theorem signatures; actual nonabelian S3 specialization; explicit noncommuting S3 witnesses; empty graph, isolated vertices, and empty surplus-family regressions
- No forbidden proof tokens in the production source
- Focused tactic-pattern scan: no repeated patterns at repository thresholds
- New blueprint fragment rendered to one page and visually inspected; no overfull boxes
- Standalone paper-gap note rendered to two pages and visually inspected; no overfull boxes

No full repository build, aggregate checkdecls run, or remote CI pass is claimed. Shared import routers and blueprint inclusion routers are deliberately untouched for parent integration. Only the new module, test, blueprint fragment, paper-gap note, and this audit are in the packet.
