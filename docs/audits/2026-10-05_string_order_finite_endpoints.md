# Finite physical endpoints for string order

Source: `Papers/0802.0447/StringOrder-v10.tex`, lines 112–122, 155–162,
241–291. Base: `8fd2b5d70fe39dd8aa464d13fd68a15f58472323`.

## Mathematics and hypotheses

For a matrix family A and an invertible stationary matrix Ω, set

S_n(Ω) = span { A_σ Ω A_τ† : |σ| = |τ| = n }.

Stationarity E_A(Ω) = Ω gives S_n(Ω) ⊆ S_(n+1)(Ω) by appending the
same physical letter to both words and summing. Prefixing independent letters
gives the recurrence S_(n+1)(Ω) = span { A_i X A_j† : X ∈ S_n(Ω) }.
Consequently equality at two consecutive steps implies equality at every later
step. If a length-N word span is full, every target X is realized at that length
by two-sided multiplication with X Ω⁻¹ and I, so S_N(Ω) is full. Strict
dimension growth before fullness therefore gives S_(D²)(Ω) = M_D(C).
For positive D the initial space is CΩ, of dimension one; the implementation
uses the safe source bound D² rather than optimizing it to D²−1.

Apply this once to (A, I) for the right endpoint and once to (A†, Λ) for
the left endpoint. Word reversal transports normality to the adjoint family.
The left physical operator uses transpose and physical-site reversal, with the
exact identity

tr(E_(A†,O)(Λ) Z) = tr(Λ E_(A, reverse(Oᵀ))(Z)).

Thus arbitrary virtual X,Y have physical representatives x,y on D² sites with

tr(Λ E_x E_u^N E_y(I)) = tr(Λ X E_u^N(Y))

for every physical matrix u and every individual middle length N. There is no
blocking of the middle string and no replacement of u by a tensor power.
Exact arbitrary-boundary realization uses general physical block operators.

For the source's stronger product convention, each nonzero endpoint functional
is first nonzero on a matrix unit of the block space. That matrix unit is an
existing `Matrix.finKronecker` product of one-site matrix units. Multilinearity
and the decomposition M = H + iK with H,K Hermitian then choose a nonzero
Hermitian factor one physical site at a time. Both endpoint coefficients remain
nonzero. This proves literal products of D² one-site Hermitian observables,
not merely Hermitian operators on an undifferentiated block.

The source-purity wrapper keeps D > 0, Λ positive definite, E_A†(Λ) = Λ,
E_A(I) = I, and the full simple-peripheral-eigenspace condition. It does not infer
irreducibility merely from unitality and a simple fixed space. Normality follows
from the existing primitive irreducible channel theorem applied to A†.

## Source corrections and scope

The source writes S_D in its display while stating D²-site endpoints and a
D²-dimensional growth argument. The implementation uses the safe D² bound.
The phase-adjusted vector limit is μ^(-N) E_u^N(Y) → tr(Λ V†Y) V;
the corresponding unadjusted complex correlator need not converge.

The fixed physical twist is retained throughout. This component does not alter
`HasStringOrder`, does not add a parallel string-order predicate, and does not
identify a scalar twist with a nontrivial physical symmetry. The independent
projective-twist correction is part of the same integrated String Order batch.

## Owners and unchanged extractions

- `MPS/Core/ObservableTransfer` receives the existing physical-observable
  definitions and elementary lemmas byte-for-byte from `RFP/ZeroCorrelationLength`.
  The previous owner imports the new lightweight owner. There is one definition.
- `MPS/Core/Blocking` receives
  `Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose` with its complete
  declaration and body unchanged. `ParentHamiltonian/PGVWC07CutRank` explicitly
  imports that owner. There is one definition.
- `PhysicalStringEndpointSpan` proves stationary-weight endpoint fullness.
- `PhysicalStringBlockEndpoints` proves exact left/right realization and literal
  Hermitian product-endpoint nonvanishing.
- `PhysicalStringBlockOrder` assembles the source canonical spectral assumptions
  and the positive limiting magnitude. This analytic assembly is not yet checked.
- The canonical purity proof is shared in `PureTwistedSpectrum`; existing public
  signatures in it and `PhysicalStringSelectionRule` are unchanged.
- The generic vector limit in `PhysicalStringAsymptotics` replaces the repeated
  scalar-endpoint argument without changing its existing public signature.

The preservation hashes and reverse consumers are recorded in the accompanying
validation JSON. Structural checks found no TNLean import cycle.

## Validation boundary

Four actual files passed Lean 4.35.0-rc3 with the package options, one thread,
and warnings treated as errors:

1. `MPS/Core/ObservableTransfer`
2. `MPS/Symmetry/PhysicalStringEndpointSpan`
3. `MPS/Core/Blocking`
4. `MPS/Symmetry/PhysicalStringBlockEndpoints`

The algebraic endpoint check used the source-matched, already checked lightweight
`StringOrderDefs` from the same batch's phase correction. That integration
dependency is explicit in the validation JSON; it is not claimed to match the
pre-correction base copy.

References sections were added to the new module headers after the focused checks.
The theorem and proof text is unchanged; checked and current source hashes are
recorded separately.

The modified analytic source files, source-purity wrapper, complete
`PhysicalStringBlockOrder`, reverse consumers, root aggregate, blueprint and
checkdecls are not yet checked. They must not be marked complete based on the
four focused passes. No cold build, publication, pull request or issue change was
performed for this checkpoint.
