# Two-family entropy integration

The generic theorem and physical regional-density proofs belong to QICLean.
This consumer uses the existing finite-domain model data
`OrderedTwoFamilyPartition`, `earlierSameFamily`, `reducedState`, and `regionalEntropy`.

The generic adapter `Geometry.OrderedTwoFamilyPartition.entropy_le_residual_add_half_sum`
formalizes
[area-law Lemma 11.1](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L26-L69)
for a pure state on an arbitrary finite tensor product, with site-dependent
local dimensions. It takes a normalized pure state, the existing labelled
disjoint partition and one information bound per piece, against the entire
exterior-plus-earlier-same-family region. Its conclusion is
`S(A) ≤ S(D) + (1/2) ∑ i, ε i`. No Hamiltonian, gap, geometry, nonempty-set or
error-sign hypothesis is added.

`regionalEntropy_le_residual_add_half_sum` is its specialization to a finite
domain in `ℤ × ℤ` with one local dimension `q`. It identifies the
already-defined regional entropy with QICLean's construction. Neither model data
nor generic entropy proofs are duplicated.

The shuffled-label regression uses three singleton pieces in a four-site system,
with family labels `1,0,1`, a nonempty exterior, and the true same-family past
`{0}` for piece `2`. It exercises the full exterior-plus-past estimate.
