# Exact small-size approximation: checked local downstream integration

## Scope

The authored module `TNLean/PEPS/Approximation/ExactSmallSizeApproximation.lean`
proves the pointwise and uniform finite-size approximation corollaries against
the native model interface owned by TNLean #8788. It does not restate, replace,
or edit that interface and does not prove `PolynomialPEPSApproximation`.

For `q > 0`, `0 < L ≤ L₀`, a real exponent `c ≥ 0`, any previous prefactor `C`,
and a unit vector `Ω`, the conclusion is
`HasPEPSApproximation (max C (q ^ (L₀ * L₀))) c L q Ω`.
The witness has the exact coefficients of `Ω`, unit norm, nonzero contraction,
and normalized error zero at phase zero. No Hamiltonian or gap assumptions
are needed for this finite-size result.

## Uniform-quantifier corollary

`TNLean.PEPS.Approximation.exists_uniform_small_size_approximation` fixes a
positive `q`, a threshold `L₀`, a nonnegative real exponent `c`, and a
previous prefactor `C`. It chooses one positive `C' ≥ C` before all sizes
`2 ≤ L < L₀` and all unit vectors, then proves the native approximation
predicate throughout that range. The witness is `max C (q ^ (L₀ * L₀))`.
An additional consumer makes explicit that the same constant can be chosen
before each Hamiltonian and ground vector. This closes the finite-range
quantifiers; it does not establish the large-size theorem.
