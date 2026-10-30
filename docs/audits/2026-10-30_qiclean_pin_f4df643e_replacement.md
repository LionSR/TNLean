# Declarations replaced by the QICLean pin f4df643e

Date: 2026-10-30.

This audit records the two TNLean declarations removed when the QICLean pin
moves from `14ecc5b64bb61cccb01a6583bbab3252bee1486b` to
`f4df643ec799b0a69859dc54d2886cf0c678f3b5`. QICLean now defines both under the
same full names, so keeping the TNLean copies would make the root import
declare each name twice.

## Replacements

| Removed TNLean declaration | QICLean declaration | QICLean source |
|---|---|---|
| `Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose` (`TNLean/MPS/Core/Blocking.lean`) | Same name | `QICLean/Kraus/Injectivity.lean`, QICLean #988 |
| `WordMultiplicity.wordCoefficient` (`TNLean/Algebra/TwoMarkerScalarRecovery.lean`) | Same name | `QICLean/Algebra/WordCoefficient.lean`, QICLean #1005 |

The block-injectivity statements are identical, and the proofs differ only in
`=>` versus `↦`. The two coefficient definitions are the same sum over ordered
words with the prescribed letter counts. TNLean writes the filter under
`by classical; exact`, while QICLean writes it under `open Classical in`. Both
choose the decidability of the count equation classically.

`TNLean/MPS/Core/Blocking.lean` already reaches `QICLean.Kraus.Injectivity`
through `QICLean.Kraus.Blocking`. `TNLean/Algebra/TwoMarkerScalarRecovery.lean`
now imports `QICLean.Algebra.WordCoefficient`. The consumers keep their full
names, and so do the blueprint tags in
`ch12_symmetry_string_order_finite_endpoints.tex` and
`ch35_two_marker_scalar_recovery.tex`.

## Other names in the range

The range adds 167 declaration names and removes four:
`hermitian_fixed_eq_scalar_of_irreducible_unital`,
`rank_weighted_sum_of_injective_monomials`, `reindexStarAlgHom` and
`reindexStarAlgHom_apply`. TNLean main uses none of the four.

QICLean #985 adds `GaussianFilter.commutatorCLM` with `H * W - W * H`. TNLean
keeps `TNLean.Lattice.commutatorCLM` with the opposite order `M * O - O * M`.
The full names differ, so they do not clash at the root. Inside
`namespace TNLean.Lattice` with `open GaussianFilter`, however, an unqualified
`commutatorCLM` becomes ambiguous in any file that also imports
`QICLean.Analysis.GaussianFilter.CommutatorSeries`. No module on main does so
yet, so this change leaves the definition in place.

## Verification

The two edited modules and the four consumers of the moved names
(`TwoWindowPolynomialRecovery`, `WStateCanonicalBound`,
`PhysicalStringBlockEndpoints` and `PhysicalStringBlockOrder`) were compiled
with the package options. The QICLean modules `Kraus/Injectivity` and
`Algebra/WordCoefficient` were taken at `f4df643e`, and every other module
from the warm build at the previous pin. `scripts/check_docbuild_manifest.py`
passes. The full build at the new pin is left to CI.
