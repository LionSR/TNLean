# Physical support transport for general-group bond separation

Source: [SCP10, Observations 6.4–6.5, lines 1765–1880](https://github.com/LionSR/TNLean/blob/3e16cc3db55b962fdc68ebd93cbf2a696339fd0d/Papers/1001.3807/paper_v3.tex#L1765-L1880). Tracker: [#8676](https://github.com/LionSR/TNLean/issues/8676).
This extends the canonical-averaging packet frozen at `d77962a45e20782455b55bd4bab9d69871606223`; its earlier audit remains a record of that packet's narrower scope.

## Actual physical theorem

`exists_regularGraphPhysicalSupportIsometry` starts with arbitrary vertex-dependent physical spaces and site tensors on a finite simple graph. Its only substantive site hypothesis is local `IsGIsometric` for the explicitly bundled regular incident representation. The finite group need not be abelian. A single finite surplus index set K specifies the uniform bundle alphabet X = G × G^K on each edge.

The theorem derives positive local factors c_v and returns an actual Hilbert-space `LinearIsometry` I on the product of the original physical site ranges. It identifies I with the explicit operation

- local normalized adjoints J_v = c_v^(-1/2) T_v*;
- followed by the vertex-local relative-coordinate permutations from the canonical packet.

It evaluates this isometry on the actual original graph state, with its physical-support membership supplied by a proved contraction identity. The result is exactly

I Ψ_a = (∏_v √c_v) (√D)^|E| Ψ_single ⊗ Ω, where D = |G^K| and ‖Ω‖² = 1.

Every original physical index, every residual endpoint coordinate, and every scalar factor is retained. The companion `exists_regularGraphPhysicalDisentangler` also states local physical-range overlap preservation, global product-range overlap preservation, the actual state norm equality, and the coefficientwise factorization. These are derived conclusions, not user-supplied hypotheses.

## Proof path

1. `GIsometricSupportCoordinates` generalizes the existing torus accessibility calculation. Local G-isometry and unitarity of the incident symmetry give T_v* T_v = c_v P_v. Consequently J_v T_v = √c_v P_v, and J_v preserves all inner products on the actual local range.
2. `GraphPhysicalMap` handles products of matrices with vertex-dependent alphabets. It proves that the actual bond contraction is in the range of the product site map, by applying that map to the explicit sum of basis vectors with equal labels at the two endpoints of each virtual bond. It also proves the same membership in the Hilbert-space realization.
3. Local physical maps commute with the actual virtual-label contraction. Their local range-isometry identities imply product Gram equality and hence global overlap preservation on the product physical range.
4. `RegularGraphPhysicalBlocking` derives the bundled incident representation's unitarity from its actual permutation entries. Applying the normalized adjoints to the original network gives the canonical bundled network with exactly ∏_v √c_v. The already proved physical Bell separation supplies the remaining factor (√D)^|E|.
5. `coordinateSupportIsometry` converts the derived inner-product equality to a genuine `LinearIsometry`, with a theorem equating its action to the same explicit coordinate map. The capstone applies it directly to the original graph vector.

No ambient physical surjectivity, supplied physical-support membership, block Gram formula, global equality, state equivalence, or Bell-factorization premise is used. The support restriction is exactly the permitted restriction of Observation 6.4, now established for the actual network.

## Scope still open

Physical dimensions, tensors, and positive local normalization factors may vary with the vertex. The graph can be disconnected, empty, or contain isolated vertices. Bundle multiplicity is uniform across edges, and this is an ordinary untwisted finite-simple-graph contraction.

The theorem does not yet identify the actual 2×2 fine-lattice block contraction with a bundled coarse graph. The remaining Observation 6.6 work is geometric reblocking, deriving the block hypotheses from the original fine sites, retaining internal block factors and all seam/boundary indices, and identifying the final coarse tensor with the original site tensor when that comparison is claimed. Native periodic presentations with parallel edges or self-loops and inserted closure sectors require their own explicit treatment. No unrestricted renormalization-fixed-point completion is claimed.

## Validation

The new dependency closure contains 138 TNLean sources: 134 pre-existing sources exactly match the independently audited `peps-completion-validation` donor; the four owned sources are the canonical module plus the three new extension modules. The pinned QICLean source closure contains 21 modules from revision `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`, using the same source-verified dependency overlay as the canonical packet. Artifacts were written only to a private overlay. No Mathlib rebuild or shared artifact mutation occurred.

Strict checks all pass with `autoImplicit=false`, `relaxedAutoImplicit=false`, `pp.unicode.fun=true`, `maxSynthPendingDepth=3`, `linter.mathlibStandardSet=true`, and `warningAsError=true`:

- `GraphPhysicalMap`: 3.06 seconds
- `GIsometricSupportCoordinates`: 3.47 seconds
- `RegularGraphPhysicalBlocking`: 6.68 seconds
- Previous canonical regression: 2.48 seconds
- New physical-support regression: 4.39 seconds
- Six new guarded axiom reports, including the actual Hilbert-space capstone: standard `[propext, Classical.choice, Quot.sound]` only
- All 20 new blueprint declaration references checked directly by Lean
- No forbidden proof tokens in the new production files
- Focused tactic-pattern scan on all four owned production files: no repeated patterns at repository thresholds
- Both blueprint fragments rendered together, with their cross-reference checked and all three PDF pages visually inspected; no overfull boxes
- Updated standalone paper-gap note rendered to two pages and visually inspected; no overfull boxes

The regression constructs actual G-isometric tensors by embedding canonical sites into a larger physical alphabet with one unused direction. It proves ambient surjectivity is false and nevertheless obtains the physical norm-preserving operation. A genuine one-edge S3 example instantiates this construction; generic graph tests retain vertex-dependent alphabets. Thus the test does not silently restore the excluded surjectivity premise.

All new production declarations are covered by the new blueprint fragment. No full aggregate build or checkdecls pass is claimed. The repository-wide source-grep synchronization check also sees unrelated dependency declarations unavailable in this worktree's source search and is not reported as passing; the new tags were verified directly against compiled Lean declarations. Shared imports, blueprint inclusion routers, and generated declaration lists remain untouched for integration.

## Optional integration cleanup

The generic normalized-adjoint theorem is the abstraction of the earlier torus-specific proof. After importing `GIsometricSupportCoordinates`, the proof of `IsGIsometric.exists_accessibleVirtualSite` in `RegularTorusSite` can use `ha.exists_accessibleCoordinates torusLegRep_leftRegularMatrix_unitary`. This removes the duplicated normalization argument. The existing file is deliberately untouched under the assigned new-files-only scope.
