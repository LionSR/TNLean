# GLM23v3: arbitrary mixed endpoints and extended parent interactions

## Source and scope

The source is `Papers/2203.12563/REsubmission.tex`, version 3, as recorded in
`Papers/NOTICE.md`. Its SHA-256 is
`c820b20187584d441c1a40ef80fdccbc8a2aad819ac6673464c6b913c28fa58c`.
The construction is Section 5, particularly the mixed tensor and inserted weight
at lines 1586–1601 and the endpoint Hamiltonian argument through line 1692.
This is a continuation of the paper-wide coverage inventory, not a replacement
for that inventory or a claim that the classification theorem is complete.

The endpoint tensors are arbitrary injective tensors in physical-support
coordinates: endpoint p has bond dimension D_p and physical dimension D_p².
Reduction from an arbitrary original physical alphabet to these coordinates is
outside this deliverable. Neither endpoint is required to be a fixed-point
tensor. Both dimensions are positive in the two-endpoint interpolation results.

## Dependency chain

1. `MixedEndpointInterpolation`: retain the actual endpoint matrices in the two
   diagonal sectors and put matrix units in the off-diagonal sectors. Derive
   injectivity of the combined alphabet. Insert
   W(γ) = (1−γ)I_D₀ ⊕ γI_D₁ on the outgoing virtual bond; prove interior
   injectivity and continuity directly.
2. `MixedEndpointSupport`: derive injectivity of the two-site boundary map
   X ↦ (tr(Aⁱ W Aʲ X))ᵢⱼ from injectivity of A and W ≠ 0, including singular W.
   The extended support has constant dimension D² and a continuous orthogonal
   projector. In the interior it equals the canonical support of A(γ).
3. `MixedEndpointEmbedding`, `MixedEndpointSectors`,
   `MixedEndpointReducingSectors`, and `MixedEndpointCornerSupport`: identify
   actual endpoint embeddings and physical row/column sector projections.
   Derive their action on boundary matrices and the embedded canonical support.
4. `MixedEndpointProjectorComparison`: prove the concrete local projection and
   positive-operator inequalities. The two outer-sector penalties are bounded
   by neighboring extended interactions after periodic placement.
5. `PhysicalReindexProjection`, `MixedEndpointSwap`, and
   `MixedEndpointRightComparison`: transport this calculation to γ = 1 through
   the actual unitary physical-sector exchange. No second endpoint comparison
   is assumed.
6. `RingEndpointComparison` and `RingEndpointRightComparison`: sum the actual
   periodic local inequalities to obtain H′ ≤ K ≤ 3H′ for every N ≥ 2, including
   the two-site ring. Derive equality of kernels, the unique periodic ground
   line, and a uniform positive endpoint gap. The canonical endpoint gap comes
   from injectivity via the existing compact-family gap theorem applied to a
   constant family; it is not an input assumption. A common positive bound
   works for both endpoint parameters, with no assertion about other γ here.
7. `MixedEndpointExtendedBoundary`, `Core/InsertedLeftInverse`,
   `MixedEndpointIntersection`, `MixedEndpointRestriction`, and
   `MixedEndpointOpenKernel`: construct the actual inserted boundary map at
   every length, derive its rank D² for N ≥ 1, prove the intersection property
   for singular nonzero W, and identify the kernel of the N−1 nonwrapping
   parent terms for N ≥ 2. Its projector is continuous for each fixed length.

The first seven mathematical stages comprise 17 production modules. The
regressions are `TNLeanTest/MixedEndpointComparison.lean` and
`TNLeanTest/MixedEndpointPhase.lean`. Blueprint leaves are
`ch30_mpo_mixed_endpoint_interpolation.tex`,
`ch30_mpo_mixed_endpoint_comparison.tex`, and
`ch30_mpo_mixed_extended_open.tex`. The tensor identity A(γ) = A W(γ) uses Tenkz
with an explicit physical pair index and one internal virtual contraction.

## Boundaries of the claims

- The periodic endpoint gap is uniform in N. Fixed-length support continuity
  alone does not yield a thermodynamic gap near the endpoints.
- The open-chain kernel keeps both free virtual boundary indices and dimension
  D². It is not replaced by the smaller embedded endpoint kernel.
- No whole-interval uniform gap, full MPO symmetry along the interpolation,
  mixed-pentagon classification, or full phase equivalence is asserted here.
- The separate continuation toward endpoint open-chain bounds requires concrete
  termwise boundary-normalization and exterior-spectator identities. Equality
  of full-chain kernels alone is insufficient for that comparison.

## Validation ledger

As of 5 October 2026, the frozen source cone has an independent mathematical
review, exact source/reverse-blueprint coverage, a rendered and visually
inspected Tenkz diagram, and clean changed-prose and whitespace checks.
Thirteen of the seventeen production modules have passed targeted Lean
elaboration: interpolation, support, embeddings, sector reduction, corner
support, left local comparison, physical reindexing, endpoint swapping,
inserted left inverses, extended boundary rank/continuity, intersection, and
contiguous restriction. The final restriction source also removes four
unused-binder warnings and awaits rechecking. Right local comparison, both
periodic endpoint modules, the open-kernel capstone, and both strict regressions
still require validation before this candidate is treated as verified. Full
exact-head CI and final review remain required before integration.
