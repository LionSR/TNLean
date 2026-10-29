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

The public `uncleTwoWallTrial_append_apply` evaluates the general trial on
the actual nested five-way Fin.append configuration, giving exactly the five
List.ofFn coefficient words. `uncleConfigSegment_eq_drop_take` identifies
numbered physical words with their exact list slices. This proves the
pointwise source-to-five-segment cast identity and
`norm_uncleTwoWallTrialSource_eq`: the actual source norm equals the actual
five-segment norm. The cast is the proved total-length equality for N>0,
not an assumed isometry or approximate factorization.

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

## Exact cyclic norm partition

The existing three-site canonical coordinate helpers are extracted from
`LocalSupportTransport.lean` into `CyclicRestrictionNorm.lean`, generalized
to all L≤T and promoted for their actual second consumer. The old three-site
proof keeps using them. No parallel coordinate equivalence is introduced.
The new raw identity sums the actual restriction norms with multiplicity
d^L, including zero physical dimension and empty windows. For d nonzero,
the actual averaging normalization divides out that multiplicity exactly.
Independent source review checked the configuration bijection, replacement
identity, sum order and empty-index cases; no local Lean invocation was run.

## Remaining work and verification boundary

`UncleTrialLocalization.lean` now derives the full global cyclic cancellation.
Numbered physical segments are defined by their actual finite coordinates.
A generic inside/outside segment calculation separates a varying pair from
its fixed exterior. The five nonwrapping regions use the two moving-wall
cancellations and the existing pure A/B local-kernel inclusions. The periodic
bond at site 6N rotates the last and first A letters together by trace cyclicity.
Three existing wrapping-site evaluation lemmas are promoted for reuse rather
than copied.

The exact surviving set is {N-1,2N,4N-1,5N}; its cardinality is proved to be
four for N positive. Every cyclic local projector outside this set kills the
actual source trial. Expanding the actual uncle Hamiltonian and deleting
these zero summands proves H phi is exactly the sum of its four endpoint
contributions. No support condition is supplied as a hypothesis. The four
endpoint contributions still require asymptotic estimates.

`UncleTrialEnergy.lean` derives the actual local operator's contraction directly
from its isometric conjugation of an orthogonal projector. It proves pointwise
norm contraction, operator norm at most one, and
Re inner(hv,v)=norm(hv)^2 in [0,norm(v)^2]. The latter uses the existing Mathlib
projection quadratic-form theorem, not a supplied positivity premise.

Combining this with the derived global localization gives the exact actual
trial energy d^(-2) times the sum, over the four endpoint bonds and exterior
configurations, of norm(h R phi)^2. Contraction bounds it by the same sum of
norm(R phi)^2. These are finite identities and inequalities with no supplied
energy/support/gap hypothesis. They do not yet prove the source O(N) rate;
that requires actual pinned-wall endpoint-state estimates.

`UncleTrialPinnedWalls.lean` now derives those endpoint residual expressions.
The one-wall concatenation identity splits walls inside/outside a chosen end.
At each cut the pure A/A or B/B contribution is killed by the actual local
projector. This leaves A_i R_j, R_i B_j, B_i L_j, or L_i A_j respectively.

Four coordinate theorems apply this to the actual cyclic trial restrictions
at N-1,2N,4N-1,5N. Their pinned sites are N,2N,4N,5N. The two R endpoints
retain exactly the L-wall sum on 4N through 5N; the two L endpoints retain
exactly the R-wall sum on N through 2N, using rectangular trace rotation.
All fixed exterior words are explicitly numbered physical segments.

`uncleTrialPinnedEndpointState` records these four explicit local vectors.
Their projected images equal the actual endpoint residuals, and the actual
trial energy is bounded by d^(-2) times their squared-norm sum. This removes
one moving-wall sum before contraction, so the remaining estimate concerns
actual one-wall vectors rather than the original two-wall trial. No support
or rate premise is introduced. The remaining O(N) step is to estimate these
explicit finite norms using the parallel one-wall Gram/mixed-map calculation
and the source normalized-transfer estimates. Norm growth, small ground-sector overlaps,
generic nonzero leading coefficients, removal of the complete ground
projection and the finite-dimensional variational spectral conclusion
remain open in this slice. The one-wall transfer recursion is parallel work.

No local Lean invocation, compilation or build was run, as requested.
Hosted CI checked exact Lean head `eabb087703ecf9389c6c018b9a5a9d4729d18d4c`:
job `123488428555` completed the full 14,995-job build and all strict checks
on eight changed source files successfully. The six finite trial Blueprint
entries are therefore marked Lean-checked. This validates the finite trial,
localization, cyclic norm partition, quadratic energy and pinned residuals;
it does not validate a subsequent asymptotic draft or complete gaplessness.
The PR remains draft pending integration, and #10286 stays open. Source/API,
import, formatting, prose, integrity and diff checks also pass. No placeholders,
axioms or persistent Lean fixtures are added.
