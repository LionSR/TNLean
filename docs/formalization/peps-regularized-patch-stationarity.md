# Coordinate first variation and canonical final-state marginals

This finite-dimensional leaf of [TNLean #8767](https://github.com/LionSR/TNLean/issues/8767)
extends the actual regularized minimum with one-coordinate variations and the
canonical reduced states of its final normalized vector. It independently
formalizes mathematics from `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`;
no upstream Lean proof text is reused.

## Source boundary

The September 24, 2026 manuscript *Polynomial PEPS approximation of gapped
square-grid ground states* supplies the following passages in
[`03-patches.tex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex):

- [Lines 68–99](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L68-L99): independent densities, the ordered product, normalization, and marginals of that same final vector.
- [Lines 134–149](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L134-L149): unitary variation of one coordinate, covariance of its shifted power, and differentiation of the actual filtered output.
- [Lines 116–132 and 150–168](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L116-L168): trace stripping and descending commutation, which remain outside this leaf.
- [Lines 170 onward](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L170): diagonal simplex variation and later estimates, also outside this leaf.

The first-variation theorem below differentiates the squared norm rather than
the source's logarithmic norm. It gives the unstripped identity at every actual
feasible minimizer, without assuming the later descending induction. It does
not assert the source's commutation conclusion.

## Actual coordinate curve and ordered derivative

Use the existing native regional coordinates and identity extension. With
`Kⱼ = (xⱼ + bI)^(-aⱼ/2)` and `Lⱼ = ι_Xⱼ(Kⱼ)`, the actual output is
`Ψ(x) = L_(m−1) ⋯ L₀ Ω`. Every coordinate has its own positive semidefinite
trace-one matrix, even when regions repeat.

`RegularizedPatchCoordinate.lean` updates only occurrence `j` to `UxⱼU*`.
It proves feasibility and exact shifted-power covariance for every unitary
`U`, positive shift `b`, feasible tuple, and arbitrary real weights. The
linear insertion is

`Iⱼ(K) = (L_(m−1) ⋯ L_(j+1)) ι_Xⱼ(K) (L_(j−1) ⋯ L₀) Ω`.

Its definition replaces one factor in the original reverse index-ordered
product, not in a reordered or commuting surrogate. Inserting `Kⱼ` recovers
`Ψ(x)`, and the actual updated output is `Iⱼ(UKⱼU*)`.

`RegularizedPatchStationarity.lean` takes a regional skew-Hermitian `B` and
uses the feasible curve `U(t) = exp(tB)` for real `t`. It proves

`d/dt Ψ(x^(j,U(t))) at t = 0 = Iⱼ(BKⱼ − KⱼB)`.

If the tuple is feasible and satisfies `IsMinOn` for the actual objective,
Fermat's theorem for the squared norm gives

`Re ⟨Ψ(x), Iⱼ(BKⱼ − KⱼB)⟩ = 0`.

There is no optimizer selection, smooth dependence on the regulator, or
assumed stationarity field. The proof differentiates exponential conjugation,
not the matrix-power function at a varying matrix.

## One final state and the existing partial trace

`RegularizedPatchMarginal.lean` uses the explicit equivalence between a
configuration on the univ subtype and the corresponding global dependent
configuration. `dependentGlobalConfigIsometry` is the induced linear isometry.
This coordinate identification does not introduce another physical state model.

For the existing normalized output `φ = normalizedRegularizedPatchOutput …`,
the regional matrix is exactly the existing `FiniteProduct.reducedPure`
applied to the coordinate image of `φ`. Every region uses this same `φ`.
It is not a marginal of the intermediate vector preceding that region's filter,
and it is not a freely supplied trace-pairing hypothesis.

For every complex regional matrix `K`, the general expectation theorem states

`⟨ξ, ι_X(K) ξ⟩ = Tr(reducedPure(Jξ, X) K)`.

This equality is complex-valued, without a Hermiticity assumption or a real-part
projection. It fixes the inner-product orientation and the pure-state outer
product. The canonical reduced states are positive semidefinite. For a unit
input, nonnegative weights, positive shift, and feasible tuple, each has trace
one by the existing normalization theorem. At every feasible minimizer the
same vector is `φ = N^(-1) M(x) Ω`.

## Degenerate cases and regressions

The statements allow varying finite local dimensions, singular densities, zero
weights, empty regions, and repeated regions. A unit input supplies the
nonzero global space when normalization is needed. No extra nonempty-local-basis
hypothesis is added. With no coordinates there is no selected `j`; the marginal
statements still apply to the identity product.

The post-build strict regression targets are:

- `TNLeanTest/RegularizedPatchStationarity.lean`: an actual feasible singular
  qubit density with a skew-Hermitian generator has real first-variation pairing
  `3/8`, and therefore cannot be an actual minimizer. Feasibility alone is
  insufficient for stationarity. It also checks two occurrences of the same
  region: updating index zero leaves index one unchanged, and insertion
  remains `I₀(K) = L₁KΩ`, `I₁(K) = KL₀Ω` in their original positions.
- `TNLeanTest/RegularizedPatchMarginal.lean`: dependent local dimensions two
  and three, an empty-region density, and a complex-phase state with Pauli-Y
  expectation `2` rather than the `−2` obtained by reversing its outer product.
  The empty-family case also checks the canonical marginal for the identity
  product directly.
- `TNLeanTest/RegularizedPatchZeroWeight.lean`: zero-weight
  behavior, including a minimizing tuple whose independent density is not
  forced to commute with its final marginal.

The blueprint diagram contracts the actual ordered insertion on the full
global Hilbert space. Reading from the input on the right, the lower-index
product acts first, the identity-extended commutator second, and the higher-index
product last. Its sole open index is the global output; its three internal
indices are global configurations. In particular, the drawing never presents
the outer products as operators supported on the selected region.

## Dependency and verification boundary

The integration base is published but unmerged
[TNLean #8822](https://github.com/LionSR/TNLean/pull/8822), revision
`e9311cbbaf55517308f416b008df5ddafcc047c9`. It is not an
accepted-main claim. The QICLean dependency remains accepted revision
`378bef486fc0241dee8ad875ccaf659d51d33ac9`; this leaf does not depend on the
pending QICLean #577 extraction. Generic trace-duality and later optimization
engines remain under [#8741](https://github.com/LionSR/TNLean/issues/8741) and
[#8744](https://github.com/LionSR/TNLean/issues/8744).

The distinct provenance shard
`docs/provenance/openai-math.d/regularizedPatchStationarity8767.json` has 18
original-proof rows. They remain `planned`/`proposed` with pending verification
until immutable source and exact native evidence are published. The earlier
minimum's verification records are not reused as evidence for these declarations.

The three production modules, regenerated area-law router, and all three
regression modules passed serial strict checks with package options, Mathlib
standard linters, warnings as errors, and a 90-second limit per invocation.
The author verified unchanged source closures and all 18 exported-name axiom
reports contain only stock axioms. The final source hashes were checked again
before adding the eight auxiliary statement/proof completion badges.

The pinned production tenkz renderer passed cold/warm SVG checks, with identical
warm bytes and modification time. The ordered-insertion audit and source lint
have zero findings. A focused four-page PDF containing the minimum and this
section was rendered twice and visually reviewed; the production SVG was also
visually reviewed. The source-only blueprint declaration check used all 983
byte-verified files of the accepted QICLean pin. These are local scoped checks.
No full Lake build, aggregate `checkdecls`, full blueprint web/PDF build, or
exact-head CI pass is claimed. Diagram and source-only checks cannot replace
those gates. Textual documentation and diagram evidence is retained in
`docs/provenance/evidence/regularizedPatchStationarity8767/docs/`; rendered PDFs
and screenshots remain local visual QA artifacts.

This leaf stops before trace-duality converses, stripping outer conjugations,
descending local commutation, diagonal KKT conditions, excitation energy,
regulator growth, rank/error bounds, and the full Proposition 4.1. It never
asserts pairwise commutation of filters.
