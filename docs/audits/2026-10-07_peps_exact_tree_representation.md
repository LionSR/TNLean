# Exact spanning-tree PEPS construction

## Scope and mathematical source

This note describes the finite-size construction in the September 24, 2026
manuscript *Polynomial PEPS Approximation of Gapped Square-Grid Ground States*.
It is the exact small-size slice of TNLean issue #8773, within the PEPS
approximation tracker #8736. It does not prove the large-size analytic or routing
parts of the main approximation theorem.

Immutable mathematical source:

- Repository: `openai/math`
- Commit: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`
- Blob: `94dc6bfdb49e83dd23316c0fdf3ffd1798bba5ef`
- File: `preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/07-assembly.tex`
- [Exact construction, lines 203–214](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/07-assembly.tex#L203)
- [Large-size bond expression, lines 164–177](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/07-assembly.tex#L164)

Only the mathematical manuscript was consulted. No original OpenAI Lean source
was copied or used. The construction uses existing TNLean native tensor and
contraction definitions and Mathlib's finite-graph and finite-index APIs.

## Representation and proof obligations

For a finite connected graph `G` with at least two vertices, choose a connected
spanning subgraph `T`, a root, and one active incident edge at each vertex. A
numbered global physical configuration occupies every active bond; inactive
bonds have dimension one. The tensor at a vertex checks equality of the active
incident labels and its physical output. Exactly the root multiplies by the
coefficient of the copied configuration.

The central proof derives the contraction rather than assuming it:

1. Nonzero local entries imply all local equality constraints.
2. A shared active edge equates its two endpoint labels, independently of the
   ordered endpoint convention used by the native `Edge` type.
3. Connectivity propagates equality to all vertices.
4. The physical constraints identify the common label with the physical
   configuration being evaluated.
5. Thus the virtual sum has only one potentially nonzero summand. Its root
   factor is the supplied coefficient and its other factors are one.

The exact contraction theorem holds for arbitrary coefficients, including the
zero vector. A separate consequence proves nonzero contraction for nonzero
input. No inverse norm or assumed normalization enters the construction.
Mathlib supplies a spanning tree, so the existential theorem has exactly the
manuscript's active and inactive bond dimensions.

The rectangular grid is the box product of two finite path graphs. Positive
side lengths imply connectedness. Its vertex count gives the square bound
`q ^ (L * L)`. The square theorem works for all positive `q` and `L`; the
explicit tree-bond statement uses `2 ≤ L`, as in the manuscript's finite-size
range.

## Degenerate cases and normalization

A singleton graph is treated by its single physical tensor, with no virtual
indices. On an empty vertex set, the native empty product forces the scalar
coefficient to be one. The packet proves this fact explicitly; it does not
claim arbitrary scalar representation on the empty graph or arbitrary-vector
representation on disconnected graphs.

For a unit input in `EuclideanSpace`, equality of the native coefficient
functions proves equality of the Hilbert vectors. The contraction norm is one,
so division by its norm is multiplication by one and the phase-one normalized
error is zero.

The uniform small-size bound is `q ^ (L₀ * L₀)`. For every real exponent `r ≥ 0`
and every previous real prefactor `C`, replacing it by
`max C (q ^ (L₀ * L₀))` gives the bound `D ≤ C' L^r` for all `0 < L ≤ L₀`.
This isolates the finite-size enlargement without assumptions on Hamiltonians.
The outer-power statement retains an arbitrary positive real exponent `χ`:
`max C ((q ^ (L₀ * L₀)) ^ (1 / χ))` supplies a prefactor for
`D ≤ (C' L^r)^χ`, including `0 < χ < 1`. It does not assume that the source's
congestion parameter was explicitly declared to be a natural number.

The `HasPEPSApproximation` corollaries are proved against the existing model
interface; no replacement approximation predicate or duplicate model is introduced.
