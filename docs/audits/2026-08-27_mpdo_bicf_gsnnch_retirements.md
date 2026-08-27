# MPDO biCF and GSNNCH four-cycle retirements (2026-08-27)

This note records the deletions made in `TNLean/MPS/MPDO` under the
pass-through exception of `docs/project_conventions.md` §Style: every removal
below has zero non-`Archive` Lean consumers after migration, and no blueprint
`\lean{...}` tag names a removed declaration. It completes the facade sweep
begun in `docs/audits/2026-08-26_mpdo_cyclic_sector_bnt_retirements.md`.

## A declaration-free import facade

| Removed module | Replacement import |
|---|---|
| `TNLean.MPS.MPDO.BiCFDerivation.Basic` | `TNLean.MPS.MPDO.BiCFDerivation.Selectors` |

The module carried no declarations; it only re-exported `Selectors`. Its single
in-library importer, `BiCFDerivation/DiagonalRestrictionCounterexample.lean`,
now imports `Selectors` directly and keeps its separate
`TNLean.Algebra.TracePairing` import: `Selectors` does not in fact reach
`QICLean.Algebra.MatrixTracePairing`, and dropping the edge left
`Matrix.trace_mul_right_eq_zero_iff` unresolved. The import closure is
otherwise unchanged. The remaining importer was the generated aggregator
`TNLean/MPS/MPDO.lean`, which was regenerated, and the bullet naming the facade
was dropped from the `BiCFDerivation.lean` module docstring.

## Overlapping-lift lemmas re-declared in an importing module

`GSNNCHFourCycleMarkov/OverlappingLiftAlgebra.lean` imports
`GSNNCHFourCycleMarkov/PositiveOverlappingProduct.lean` and re-declared three of
its private lemmas verbatim. The copies were deleted and the originals promoted
from `private` to public.

| Removed declaration | Replacement |
|---|---|
| `Matrix.leftOverlappingLift_mul` (copy in `OverlappingLiftAlgebra.lean`) | `Matrix.leftOverlappingLift_mul` in `PositiveOverlappingProduct.lean`, now public |
| `Matrix.rightOverlappingLift_mul` (copy in `OverlappingLiftAlgebra.lean`) | `Matrix.rightOverlappingLift_mul` in `PositiveOverlappingProduct.lean`, now public |
| `Matrix.rightOverlappingLift_kronecker_one` (copy in `OverlappingLiftAlgebra.lean`) | `Matrix.rightOverlappingLift_kronecker_one` in `PositiveOverlappingProduct.lean`, now public |
| `Matrix.rightOverlappingLift_smul` | none needed; the lemma had no consumer anywhere in the production corpus |

`leftOverlappingLift_star` and `rightOverlappingLift_star` stay private: they
have no duplicate and no consumer outside their own module. The
`OverlappingLiftAlgebra.lean` module docstring no longer advertises the
multiplicative properties, which now live with the originals.

## The homogeneous axis-ideal family

`BiCFDerivation/PairHomogenization/Algebra.lean` carried two parallel families
of private axis-ideal declarations: one fixing a single bond dimension `D` and
one, spelled with a `Hetero` suffix, allowing two dimensions `D₁` and `D₂`. The
bodies agreed verbatim up to the dimension binders. The equal-dimension family
was deleted and the general one renamed to the shorter spellings.

| Removed declaration | Replacement |
|---|---|
| `MPSTensor.leftAxisIdeal` at one dimension | `MPSTensor.leftAxisIdeal`, formerly `leftAxisIdealHetero`, at two |
| `MPSTensor.rightAxisIdeal` at one dimension | `MPSTensor.rightAxisIdeal`, formerly `rightAxisIdealHetero`, at two |
| `MPSTensor.fstProjection_injective_of_rightAxisIdeal_eq_bot` at one dimension | the same name, formerly `fstProjectionHetero_injective_of_rightAxisIdeal_eq_bot` |
| `MPSTensor.sndProjection_injective_of_leftAxisIdeal_eq_bot` at one dimension | the same name, formerly `sndProjectionHetero_injective_of_leftAxisIdeal_eq_bot` |
| `MPSTensor.fstProjection_surjective_of_map_eq_top` at one dimension | the same name, formerly `fstProjectionHetero_surjective_of_map_eq_top` |
| `MPSTensor.sndProjection_surjective_of_map_eq_top` at one dimension | the same name, formerly `sndProjectionHetero_surjective_of_map_eq_top` |
| `MPSTensor.matrixPairSubalgebra_eq_top_of_leftAxisIdealHetero_eq_top` | the public `MPSTensor.matrixPairSubalgebra_eq_top_of_leftAxisIdeal_eq_top`, generalized to two dimensions |
| `MPSTensor.matrixPairSubalgebra_eq_top_of_rightAxisIdealHetero_eq_top` | the public `MPSTensor.matrixPairSubalgebra_eq_top_of_rightAxisIdeal_eq_top`, generalized to two dimensions |

`matrixPairSubalgebra_algEquiv_of_axisIdealsHetero_eq_bot` was renamed to
`matrixPairSubalgebra_algEquiv_of_axisIdeals_eq_bot` in the same pass. All of
these are private to the module, so the renames are file-local.

Three public theorems were strictly generalized, dropping the hypothesis that
the two bond dimensions coincide and adding nothing:
`matrixPairSubalgebra_eq_top_of_axes`,
`matrixPairSubalgebra_eq_top_of_leftAxisIdeal_eq_top`, and
`matrixPairSubalgebra_eq_top_of_rightAxisIdeal_eq_top`. Their names,
conclusions, and docstrings are unchanged, so the faithfulness rule is
unaffected and no blueprint label was redirected: the two tagged names in
`ch13_parent_hamiltonian_block_intersections.tex` still resolve, and their prose
fixes no dimension. The equal-dimension consumers
`matrixPairSubalgebra_eq_graph_algEquiv_of_axisIdeals_eq_bot` and
`subdirect_matrix_pair_eq_top_or_eq_graph_algEquiv` reach the generalized
statements by unification at `D₁ = D₂`.

## An import edge that inverted the layering

`BiCFDerivation/Core.lean` imported `TNLean.MPS.FundamentalTheorem.ProductAlgebra`
without naming anything from it, which had the MPDO biCF derivation layer
reaching up into the fundamental-theorem layer. Dropping the edge removes
fourteen modules — ten in TNLean, four in QICLean, about 3,600 source lines —
and no Mathlib module from the compile closure of that file. Nothing was added
in its place: `Mathlib.Data.Matrix.Basis` and `Mathlib.Logic.Equiv.Fin.Basic`
remain reachable through `TNLean.MPS.MPDO.PerCopyHorizontalCF`, and
`Fintype.sum_prod_type` through `Mathlib.Data.Fintype.BigOperators`.
