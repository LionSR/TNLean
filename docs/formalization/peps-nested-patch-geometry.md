# Nested-square geometry for the PEPS patch construction

This batch isolates the finite geometry used in the proof of Proposition 4.1
of the September 24, 2026 manuscript *Polynomial PEPS approximation of gapped
square-grid ground states*. Its source is
[`03-patches.tex` at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex).
The proofs are independently written from the manuscript mathematics; no upstream
Lean proof text is reused.

## Objects and boundary conventions

The domain is the existing finite induced square-lattice domain
`Λ : Finset (ℤ × ℤ)`. Its vertices are `AreaLaw.Site Λ`; its graph and unordered
edge boundary are `AreaLaw.domainGraph Λ` and `AreaLaw.edgeBoundary Λ`.
No second lattice graph, edge convention, Hamiltonian, or support algebra is
introduced. On the original open square, the rectangular identification and
native square-grid transport remain those of the existing model and #8788.

For an arbitrary real centre `c : ℝ × ℝ` and real radius `r`, the sample is

`K(c,r) = {x ∈ Λ : |x₁ − c₁| ≤ r and |x₂ − c₂| ≤ r}`.

Both coordinate inequalities are closed. The centre need not be a lattice
site, and the square need not fit inside the physical domain. Empty samples,
clipping, holes, and disconnected finite domains are allowed. Negative radii
have empty samples. This is ambient coordinate geometry, not an induced-graph
ball; missing sites do not change the defining coordinate inequalities.

For `r ≥ 0`, there are at most `8r + 4` unordered induced edges crossing the
sample. On each integer row a horizontal crossing can occur only at one of
the two ends of the square's integer interval. At most `2r + 1` rows meet the
square; the vertical count is the same. Removing sites from the ambient
square lattice only removes possible induced crossing edges. In particular,
`0 ≤ r ≤ 2u` gives the bound `16u + 4`.

## Nested radii and edge supports

For `u ≥ 0`, set `m = floor(u / 2) + 1`, with indices `0 ≤ j < m`, and put
`rⱼ = u + 2j`, `Kⱼ = K(c,rⱼ)`. Then `m > u / 2`,
`u ≤ rⱼ ≤ 2u`, and the patches are nested in the index order.

An induced nearest-neighbour edge crossing `Kⱼ` has both sites outside every
earlier `Kᵢ` and both sites inside every later `Kₖ`. Equivalently, its two-site
support is disjoint from each earlier patch and contained in each later
patch. Therefore one edge cannot cross two different members of the family.
The separation by two units, together with a nearest-neighbour displacement of
one unit, is what makes these conclusions hold even at a nonintegral centre
and when the domain clips the squares.

The blueprint gives an exact finite example: `Λ = {0,…,10} × {0,1,2}`,
`c = (5/4,3/2)`, and `u = 4`. The three samples end at columns `5`, `7`, and
`9`. The edge from `(7,1)` to `(8,1)` crosses only the middle sample.
`scripts/test_nested_patch_geometry_diagram.py` checks the illustrated samples
using exact rational arithmetic, verifies its 33 sites and 52 distinct edges,
and checks the disjoint/contained alternatives. The diagram depicts adjacency
only; it asserts no tensor contraction or operator identity.

## Uniform scalar coefficient

For `u ≥ 4`, give the `m` patches the uniform weight `tⱼ = κ / m`, where
`κ` is any real number. Then

`∑ⱼ |∂Λ Kⱼ| tⱼ² ≤ (16u + 4) ∑ⱼ tⱼ² ≤ 36κ²`.

The first inequality uses the proved crossing-edge counts. The second uses
`∑ⱼ tⱼ² = κ² / m` and `16u + 4 ≤ 36m`. This is scalar arithmetic attached
to the actual sampled boundaries. It does not identify the weighted sum with
any Hamiltonian energy increment; that analytic argument is still required.

## Scope and verification

These are geometric inputs to the paper's patch argument. They do not prove
the Hamiltonian energy estimate, construct the low-energy filters, establish
a minimizing vector or a Schmidt-rank bound, or complete Proposition 4.1.
In particular, no energy bound is assumed as a field or replaced by a scalar
inequality with the same numerical constant.

The issue-owned provenance shard is
`docs/provenance/openai-math.d/8767.json`. Planned provenance rows are not proof
completion evidence; immutable source and build/axioms evidence must be recorded
before their status changes. The chapter's checked declarations and exact
verification commands are synchronized with the implementation before review.
