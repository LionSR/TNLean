# Actual joint open-chain active projection

This source extension addresses the inactive sector of the zero-parameter
open interaction in GLM23, arXiv:2203.12563v3, Section 5, lines 1695–1777.
It does not establish the full endpoint gap.

## Mathematical content

Write `L` and `R` for the orthogonal projections onto the full joint polar
boundary ranges, and `row₀`, `column₀` for the physical phase selectors.
The actual support is contained in each of

- `ran(L ⊗ row₀)`;
- `ran(column₀ ⊗ R)`;
- `ran(column₀ ⊗ row₀)`.

These inclusions come from the existing full joint frame factorization and
the actual inner phase-fixing identities. They are not supplied as premises.
All joint Gram entries, shared physical directions, empty labels, and zero
dimensions remain present.

For `N = n + 3`, the `n + 2` nonwrapping bond constraints use the first
one-sided product on the first bond, the last one-sided product on the last
bond, and the inner product elsewhere. Their only overlaps are row and
column selectors on interior sites. Their product `Q` is therefore an
orthogonal projection. Its range is characterized by the full first frame,
the full last frame, and both zero-phase selectors at each of the `n + 1`
interior sites. The interior alphabet is the entire original shared
physical `00` space, including unused physical directions.

The source derives `Commute Q H` and `1 - Q ≤ H`, hence `1 - Q ≤ 2 • H`.
The coefficient-one estimate is an auxiliary strengthening from the chosen
commuting constraints, not a constant attributed to the paper. The actual
Hamiltonian terms are not assumed to commute. The two-site chain is handled
separately by its one full-frame term.

## Source ownership and validation

- `Martingale/SiteProjectionEmbedding.lean` identifies the existing local
  Euclidean extension with the existing circuit matrix embedding. It gives
  multiplicativity, projection transport, one-site placement, and disjoint
  support commutation. It does not introduce another embedding definition
  for multi-site operators.
- `JointMixedEndpointOneSidedSupport.lean` derives the full one-sided support
  and the separate first/last frame commutators and local penalties.
- `JointMixedEndpointInnerConstraints.lean` combines the actual inner phase
  constraints and transports all phase commutators to the open chain.
- `JointMixedEndpointOpenSectorPenalty.lean` constructs the actual active
  projection, identifies its range, and proves the reducing commutator and
  inactive penalty.
- `TNLeanTest/JointMixedEndpointOpenSectorPenalty.lean` includes overlapping
  physical labels, an unused physical direction, zero second fibers, zero
  first fibers, empty labels, `N = 3`, and the separate `N = 2` term. Ten
  standard-axiom guards cover the main statements and the embedding bridge.

Only static source review, whitespace checking, declaration-reference
checking, and the tactic-pattern scan were performed here. No Lean compiler,
Lake build, cache mutation, blueprint build, or diagram compilation ran:
another task held the sole native validation slot. The new blueprint leaf
therefore has no completion markers yet. Native elaboration and the actual
axiom-guard outputs remain unverified.

Root imports, shared workflow lists, and the common blueprint input list
were left for coordinated integration. The new blueprint leaf is
`ch30_mpo_joint_open_sector_penalty.tex`, intended after the full-frame
reduction leaf. No MPU or PEPS source was changed.

## Remaining endpoint argument

This package does not identify or gap the active compressed Hamiltonian.
The subsequent argument must connect its actual boundary-normalized
constraints to the unchanged joint `A₀` bulk and the common ordered-pair
core family, and derive the needed uniform comparison. No per-block gap
minimum, blockwise physical orthogonality, or interior normalization is
introduced here.
