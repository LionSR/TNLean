# Orthogonalization of arbitrary nested cylinders

This development isolates the projected-image orthogonalization in the proof of
Proposition 4.1 of the September 24, 2026 manuscript *Polynomial PEPS approximation
of gapped square-grid ground states*. The exact source is
[`03-patches.tex`, lines 563–603](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L563-L603),
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proofs are independently written from the manuscript mathematics; no upstream
Lean proof text is reused.

## Existing coordinates and region support

The construction uses the existing dependent site coordinates,
`dependentRegionSlice`, `dependentSubregionOperatorLift`,
`dependentRegionOperatorLift`, and `coordinateRangeProjector`.
It introduces no new lattice, Hamiltonian, physical state, or support algebra.
The sites form a finite ordered type and each local configuration type is finite;
no positive-dimension assumption is added.

For a region `R` and an inside subspace `S`, `dependentRegionCylinder R S`
is the subspace of global vectors whose every outside-coordinate slice lies in
`S`. In tensor notation this is `S ⊗ H_(V\R)`.
The cylinder's orthogonal projector is `P_S ⊗ I_(V\R)`.
Cylinders preserve finite sums, commute with images of regional operators, and
can be written over any containing region. These facts are proved from the
native coordinate slices and identity extensions.

## The actual projected-image construction

Take an arbitrary finite monotone family `R₀ ⊆ ⋯ ⊆ R_(n−1)` and arbitrary
inside subspaces `Sⱼ ⊆ H_(Rⱼ)`. No containment or commutativity hypothesis is
imposed on the `Sⱼ` or their original projectors.
At stage `j`, form the following subspace of the current inside space:

`Wⱼ = ∑_(i<j) range(P_(Sᵢ) ⊗ I_(Rⱼ\Rᵢ))`.

Its global cylinder is exactly the span of the earlier original cylinders.
The new inside subspace is the linear image

`S̃ⱼ = (I_(Rⱼ) − P_(Wⱼ)) Sⱼ`.

This uses the orthogonal projector onto the earlier span. It does not require
that the original projectors commute. The decomposition
`Wⱼ + Sⱼ = Wⱼ ⊕ S̃ⱼ` gives mutually orthogonal global cylinders with the
same span at every prefix, including the empty prefix and the full family.
Consequently the projector onto the original total span is the sum of the
identity extensions of the inside projectors `P_(S̃ⱼ)`.
If all regions lie in `U`, that total projector is an identity extension from
`U`; its support is therefore contained in `U`.

## Inside rank is not global rank

The source defines the inside rank of a specified cylinder `S ⊗ H_(V\R)`
to be `dim S`. The construction proves `dim S̃ⱼ ≤ dim Sⱼ` directly as an
image-dimension inequality on `H_(Rⱼ)`, then sums those inequalities.
It does not obtain this bound by cancelling an outside dimension from a global
rank inequality. That distinction also handles zero-dimensional local spaces,
where an outside tensor factor may vanish and global dimension gives no
information about the inside subspace.

Repeated regions, zero inside subspaces, the empty family, and empty regions
are included. An empty region has one empty configuration and hence inside
space `ℂ`, as in the manuscript. A zero innovation contributes the zero
projector and inside rank zero.

## Two tempting substitutions fail

Let `W = span(e₁)` and `S = span(e₁ + e₂)` in `ℂ²`. Then:

- `(I − P_W)S = span(e₂)`, but `S ∩ W⊥ = {0}`.
- `(I − P_W)P_S(I − P_W) = (1/2)P_(span(e₂))`; its square is
  `(1/4)P_(span(e₂))`, so it is not a projector.

The blueprint includes a commutative square of the restricted projections:
`S → W → {0}` and `S → (I − P_W)S → {0}`. The first arrows send `e₁ + e₂`
to `e₁` and `e₂`, respectively. Both composites vanish. This uses the shared
`tikzcd` print/web renderer and has no tensor-contraction interpretation.
The projector used by the construction is the projector onto the image, not
the sandwich of the old projector by the complementary projection.

## Scope

These results supply the linear-algebra step at arbitrary nested regions.
They do not construct the source's optimizing filters, establish the spectral
inside-rank inputs, prove the approximation error, or complete Proposition 4.1.
The first-head expansion of noncommuting contractions is separate work.
The result here uses inside projectors; no formal rank-one basis expansion of
each inside projector is claimed by this batch.
