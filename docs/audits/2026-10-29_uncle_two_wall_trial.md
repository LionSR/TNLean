# Two-domain-wall trial and interior cancellation

Issue #10286; native tracker #7685. This slice stacks on the actual finite
uncle kernel construction, draft #10314, head `7a4704735`. Source:
`Papers/1210.6613/UncleHMPS.tex:254–282,773–787,1196–1316`,
standard form, equation defining phi_N, Lemma lowenergystates and Theorem gapless.

## Standing normalization matters

The general two-block discussion explicitly chooses A and B in the earlier
standard form. Both transfer operators have spectral radius one, a unique
peripheral eigenvalue one, identity right fixed point, and a faithful dual
fixed density with trace one. The blocks are distinct and block-injective,
so the mixed transfer spectral radius is strictly below one. The paper's
exp(-k) notation allows a constant in the exponential rate.

These facts are used to control long uniform padding, two-wall overlaps,
and orthogonality to the two ground sectors. Full perturbation injectivity
alone, which suffices for the finite kernel equality, does not state these
normalizations. In particular, arbitrary separate block rescalings need not
preserve the relative transfer radii used in the variational estimates.
No gaplessness theorem is asserted here with only that algebraic hypothesis.

The source's genericity step is algebraic: the leading norm coefficients
C_R and C_L are non-identically-zero quadratic functions; their zero sets
are proper algebraic exceptional sets. This slice neither proves that
nonidentity assertion nor substitutes a measure-theoretic predicate for it.

## Exact trial and local cancellation

`UncleTwoWallTrial.lean` defines the five-segment coefficient
trace(A_word * R_wall_sum * B_word * L_wall_sum * A_word). The existing
rectangular wall sum contains one wall at every possible position exactly
once. `uncleTwoWallCoefficient_eq_sum` expands both wall windows independently;
these are actual two-wall vectors rather than full uncle-tensor powers.

`uncleTwoWallTrial` takes segment lengths p,r,q,s,t. The source specialization
`uncleTwoWallTrialSource` is directly on 6N+1 physical sites. For N positive,
the five lengths are N,N+1,2N-1,N+1,N. In zero-based coordinates the R wall
moves from N through 2N and the L wall from 4N through 5N. Thus there are
exactly (N+1)^2 summands, with two long separating uniform intervals around
the periodic chain. N=0 is not used by the asymptotic source argument.

For arbitrary exterior words and a virtual linear functional, varying a
pair inside a single-wall coefficient word gives a member of the actual
two-site boundary space. The proof composes the existing bilinear boundary
product maps and uses existing matrix trace representation. Root's exact
two-site range-to-projector-kernel identity then gives actual cancellation.

Two concrete corollaries apply this to the real two-wall coefficient with
a pair entirely inside either moving interval and all exterior physical
letters fixed. In the second interval the rectangular trace identity
rotates the exterior first wall around the trace. No supplied local-kernel
condition, perturbation injectivity, normalization or gap estimate is a
premise of these cancellation results.

## Remaining work and verification boundary

The full global cyclic restriction calculation, including the nonwrapping
and wrapping uniform intervals, still needs assembly. The four bonds at
wall-window endpoints require actual estimates; cancellation alone does not
bound their total energy. Norm growth, small ground-sector overlaps,
generic nonzero leading coefficients, removal of the complete ground
projection and the finite-dimensional variational spectral conclusion
remain open in this slice. The one-wall transfer recursion is parallel work.

No local Lean invocation, compilation or build was run, as requested.
Source/API inspection, import generation, formatting, prose and integrity
checks do not establish Lean acceptance. This remains a draft proof
candidate with Blueprint notready; #10286 stays open. No placeholders,
axioms or persistent Lean fixtures are added.
