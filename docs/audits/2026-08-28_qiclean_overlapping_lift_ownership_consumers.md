# QICLean overlapping-lift ownership consumer migration (2026-08-28)

## Boundary

Generic algebra of overlapping matrix lifts and the positive-overlapping-product
quantum Markov criterion are now owned by QICLean. TNLean retains the
MPS/MPDO-facing four-cycle construction and obstruction argument.

## QICLean owners

- `QICLean.Algebra.OverlappingLiftAlgebra` owns the multiplicativity, star,
  Kronecker, sum, scalar, support-annihilation, and positivity lemmas for
  `Matrix.leftOverlappingLift` and `Matrix.rightOverlappingLift`.
- `QICLean.Entropy.PositiveOverlappingProduct` owns
  `Matrix.exists_quantumMarkovDecomposition_of_positive_overlapping_product`
  and its generic spatial-decomposition proof.

Public declaration names were preserved. The formerly private star lemmas were
promoted to the generic public API as `Matrix.leftOverlappingLift_star` and
`Matrix.rightOverlappingLift_star`.

## TNLean consumer changes

- `TNLean.MPS.MPDO.GSNNCHFourCycleMarkov.FourCycle` imports the two QICLean
  owners directly.
- The duplicate generic modules
  `GSNNCHFourCycleMarkov/OverlappingLiftAlgebra.lean` and
  `GSNNCHFourCycleMarkov/PositiveOverlappingProduct.lean` were deleted rather
  than retained as forwarding modules.
- The `TNLean.MPS.MPDO` and `GSNNCHFourCycleMarkov` aggregators no longer import
  those deleted modules.

The MPDO theorem applying the criterion to the regrouped four-site GSNNCH state
remains in TNLean.
