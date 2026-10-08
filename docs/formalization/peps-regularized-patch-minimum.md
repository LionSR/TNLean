# Minimum norm of regularized regional filters

This development isolates the finite-dimensional minimization argument in the
proof of Proposition 4.1 of the September 24, 2026 manuscript *Polynomial PEPS
approximation of gapped square-grid ground states*. The source is
[`03-patches.tex`, lines 51–114](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L51-L114),
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The variational problem and elementary bounds appear at lines 68–99;
lines 101–114 describe later estimates outside this development.
The proofs are independently written from the manuscript mathematics.
No upstream Lean proof text is reused.

## Independent densities and an ordered product

`TNLean/PEPS/AreaLaw/RegularizedPatchMinimum.lean` uses the existing finite
ordered site type, dependent local configuration spaces, and
`dependentRegionOperatorLift`. No lattice, Hamiltonian, physical state, or
alternative regional coordinate model is introduced.

For any finite family of regions `X₀, …, X_(m−1)`, the feasible set consists
of tuples `x = (xⱼ)` with `xⱼ ≥ 0` and `Tr xⱼ = 1` on the physical space
of `Xⱼ`. Each occurrence has an independent density, even if two regions are
equal. These variables are not required to be marginals of a common state.
Given a unit global Euclidean vector `Ω`, real weights `aⱼ`, and `b > 0`, set

`Lⱼ(x) = (xⱼ + bI)^(-aⱼ/2) ⊗ I_(V\Xⱼ)`,

`M(x) = L_(m−1)(x) ⋯ L₀(x)`, and `F(x) = ‖M(x)Ω‖`.

The product is the reverse of the index-ordered list. Thus `L₀` acts first.
The positive shift is taken on the full regional space, including the kernel
of a singular density. No support compression is used.

The feasible set is compact. Its nonemptiness follows from the unit vector:
a nonzero global coordinate supplies a configuration on every region, hence
a positive regional dimension and the maximally mixed trace-one density. No separate
positive-local-dimension assumption is needed. Continuity of shifted real
powers, regional identity extension, finite ordered multiplication, and the
Euclidean norm proves continuity of `F` on this set. Therefore
`exists_isMinOn_regularizedPatchObjective` supplies an actual feasible
minimizer. This existence theorem permits arbitrary real weights; nonnegative
weights enter the quantitative bounds below.

## Bounds and every minimizer

Write `A = ∑ⱼ aⱼ` and assume `aⱼ ≥ 0`. Every feasible tuple satisfies

`(1 + b)^(-A/2) ≤ F(x) ≤ b^(-A/2)`.

Each factor has upper norm bound `b^(-aⱼ/2)`. Its lower bound follows by
cancelling it with the positive power of the same shifted density and using
the upper bound `(1 + b)^(aⱼ/2)` for that inverse. Successive application
preserves the product order and needs no inter-factor commutation.

`regularizedPatchMinimum` is the infimum of the actual objective image.
Every feasible minimizer has objective value equal to this same number,
and attainment transfers both bounds to the minimum. The lower bound is
strictly positive. Dividing every feasible filtered output by its own norm
therefore yields a unit vector. At any minimizing tuple, that normalization
can equivalently divide by the common minimum. Neither uniqueness of the
minimizer nor a smooth choice of minimizers is asserted.

For `b = exp(-R)` and any real `R`, the bounds for every feasible tuple become

`(1 + exp(-R))^(-A/2) ≤ F(x) ≤ exp(RA/2)`.

For `R ≥ 0`, the minimum also satisfies
`2^(-A/2) ≤ N(R) ≤ exp(RA/2)`. Taking the source weights
`aⱼ = κ/m` gives `A = κ` whenever `m > 0`.

## Scope and edge cases

The finite-dimensional argument allows arbitrary regions, including empty
and repeated regions. It requires neither nestedness nor commutation between
filters. Empty regions have one empty configuration and physical space `ℂ`.
For `m = 0`, the empty product is the identity and the objective and minimum
are one. Zero weights and singular densities are included.
The focused regression targets also include two noncommuting filters on a
repeated region and explicit order-sensitive products.
The accompanying native tenkz diagram depicts two occurrences of one region,
with an explicit complementary identity for each filter. Its state is on the
right: `K₀` acts first, then `K₁`. The displayed qubit example uses the same
singular densities as the regression and checks the unequal `(0,1)` entries
`(K₁K₀)₀₁ = −1/4` and `(K₀K₁)₀₁ = −1/8`. The two open output indices and all
four internal contractions are stated beside the diagram source.

This result does not establish stationarity or KKT conditions, excitation
energy bounds, the later slow-growth estimate for the optimized norm,
retained-rank estimates, approximation error, or the full adaptive patch
constraint of Proposition 4.1. It supplies the minimum and its elementary
bounds, not those subsequent arguments.

## Dependencies and scope

The shifted density powers come from `QICLean/Analysis/ShiftedDensityPowers.lean`.
The minimum does not depend on cylinder orthogonalization. These results
cover the finite-dimensional auxiliary statements only; they do not complete
Proposition 4.1.
