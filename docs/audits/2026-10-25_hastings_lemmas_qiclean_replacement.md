# Hastings helper lemmas in QICLean

Date: 2026-10-25.

This audit records the removal of eight generic helper lemmas from the Hastings
area-law modules after their extraction into QICLean. Each removal landed in the
same TNLean pull request as the QICLean pin that provides the replacement, so no
intermediate commit of `main` has both or neither.

## Pin 252a7323ce (TNLean #10133, QICLean #922)

The four lemmas concern Hermitian unitary paths `t ↦ e^{iMt}` and the Gaussian
intertwiner; none uses a lattice or a support condition. TNLean used them
unqualified under `open Matrix` and `open GaussianFilter`, so with the new pin
the old names would have been ambiguous.

| Removed TNLean declaration | QICLean declaration |
|---|---|
| `TNLean.MPS.AreaLaw.Hastings.norm_hermitianUnitaryPath_sub_le` | `Matrix.norm_hermitianUnitaryPath_sub_le` |
| `TNLean.MPS.AreaLaw.Hastings.hermitianUnitaryPath_smul_one` | `Matrix.hermitianUnitaryPath_smul_one` |
| `TNLean.MPS.AreaLaw.Hastings.hermitianUnitaryPath_add_smul_one` | `Matrix.hermitianUnitaryPath_add_smul_one` |
| `TNLean.MPS.AreaLaw.Hastings.gaussianIntertwiner_add_smul_one` | `GaussianFilter.gaussianIntertwiner_add_smul_one` |

The call sites in `GaussianTimeAverage.lean`,
`BoundaryLocalization.lean` and `BoundaryFactorization.lean` use the QICLean
names. The blueprint entry in `ch35_hastings_gaussian_time_average.tex` cites
`Matrix.norm_hermitianUnitaryPath_sub_le`, and the proof-automation row in
`CLAUDE.md` names `QICLean/Analysis/UnitaryEvolution.lean`.

## Pin 8c602ab2d0 (TNLean #10143, QICLean #923 and #924)

| Removed TNLean declaration | QICLean declaration |
|---|---|
| `Matrix.PosSemidef.norm_trace_mul_mul_le` | Same name, in `QICLean/Analysis/TraceMulBound.lean` |
| `Matrix.PosSemidef.re_trace_mul_mul_self_le` | Same name, in `QICLean/Analysis/TraceMulBound.lean` |
| `TNLean.MPS.AreaLaw.Hastings.commute_reindex_one_kronecker_of_isSupportedOn` | `Entropy.commute_reindex_one_kronecker_of_isSupportedOn` |
| `TNLean.MPS.AreaLaw.Hastings.toEuclideanCLM_reindex_cutEquiv_symm` | `Entropy.toEuclideanCLM_reindex_cutEquiv_symm` |

The two trace-pairing bounds were declared in `Hastings/EffectExpectation.lean`
under the same full names as their QICLean replacements, which would clash once
pinned; their dot-notation uses resolve to the QICLean declarations unchanged.
The two cut-coordinate lemmas keep their statements apart from the namespace;
the three call sites in `SchmidtDiagonalChain.lean` use the `Entropy` names, and
the two helper `\lean` tags in `ch35_hastings_schmidt_diagonal.tex` were removed
because QICLean's blueprint documents them.

In both pins, no old full name remains in TNLean source, tests or blueprint
tags outside `Archive`, and no alias is kept. QICLean's axiom tests cover the
replacements.
