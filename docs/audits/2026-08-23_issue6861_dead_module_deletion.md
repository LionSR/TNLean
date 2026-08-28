# Issue 6861: compatibility retirement audit

This note records the compatibility decision for two TNLean-local modules from
the August 2026 mass-deletion review. The audit was repeated at the branch
point from `main`: none of the names below has a non-`Archive` Lean consumer,
and no Blueprint `\lean{...}` tag names one of them.

Repository-wide prose search finds only dated inventory snapshots in
`docs/audits/`. These records describe earlier tree states; they neither
prescribe an import nor present either module as a current public interface.

## Retired: `TNLean/MPS/Core/BlockTriangularTrace.lean`

Issue #7250 removed this coordinate compatibility module after confirming that
none of its public declarations had a non-`Archive` Lean consumer or Blueprint
tag. The removed declarations were:

- `MPSTensor.upperSum`;
- `MPSTensor.diagSum`;
- `MPSTensor.upperFin`;
- `MPSTensor.diagFin`;
- `MPSTensor.trace_fromBlocks_upper`;
- `MPSTensor.evalWord_upperSum_is_fromBlocks`;
- `MPSTensor.evalWord_diagSum_is_fromBlocks`;
- `MPSTensor.trace_evalWord_upperSum_eq_trace_evalWord_diagSum`;
- `MPSTensor.mpv_upperFin_eq_mpv_diagFin`;
- `MPSTensor.sameMPV_upperFin_diagFin`.

Issue #7135 had already completed the compatibility transition to the
coordinate-free API in `TNLean/MPS/Core/ProjectionTriangularTrace.lean`, using
an orthogonal projection and its complement. The exact replacement relation at
removal was:

| Removed coordinate declaration | Surviving replacement |
|---|---|
| `MPSTensor.upperSum` | None; construct the block matrix directly when coordinates are required. |
| `MPSTensor.diagSum` | `Kraus.diagPart` for the coordinate-free diagonal compression. |
| `MPSTensor.upperFin` | None; reindex a tensor directly when coordinates are required. |
| `MPSTensor.diagFin` | `Kraus.diagPart` after choosing the orthogonal projection. |
| `MPSTensor.trace_fromBlocks_upper` | `Matrix.trace_eq_trace_diag_of_proj`. |
| `MPSTensor.evalWord_upperSum_is_fromBlocks` | `Kraus.lowerZero_evalWord` and `Kraus.evalWord_diagPart_eq`; no individual block-coordinate wrapper remains. |
| `MPSTensor.evalWord_diagSum_is_fromBlocks` | `Kraus.evalWord_diagPart_eq`; no individual block-coordinate wrapper remains. |
| `MPSTensor.trace_evalWord_upperSum_eq_trace_evalWord_diagSum` | `Kraus.trace_evalWord_diagPart_eq`. |
| `MPSTensor.mpv_upperFin_eq_mpv_diagFin` | Pointwise use of `MPSTensor.sameMPV_diagPart_of_lowerZero`. |
| `MPSTensor.sameMPV_upperFin_diagFin` | `MPSTensor.sameMPV_diagPart_of_lowerZero`. |

The four coordinate constructors and the two individual diagonal-block lemmas
were removed with the rest of the orphan module: no consumer justified moving
them into the projection API. The surviving projection declarations provide
the coordinate-free trace and matrix-product-vector invariance results.

## Retired: `TNLean/Wielandt/RankOne/MatrixFittingRange.lean`

This module contained only deprecated aliases of QICLean-owned declarations.
Each removed compatibility name and its surviving replacement are:

| Removed name | Replacement |
|---|---|
| `MPSTensor.pow_mulVec_eq_smul_of_mulVec_eq_smul` | `Matrix.pow_mulVec_eq_smul_of_mulVec_eq_smul` |
| `MPSTensor.mem_range_toLin'_of_eigenvector` | `Matrix.mem_range_toLin'_of_eigenvector` |
| `MPSTensor.mem_range_vecMulLinear_of_transpose_eigenvector` | `Matrix.mem_range_vecMulLinear_of_transpose_eigenvector` |
| `MPSTensor.mem_range_toLin'_pow_of_eigenvector` | `Matrix.mem_range_toLin'_pow_of_eigenvector` |
| `MPSTensor.mem_range_vecMulLinear_pow_of_transpose_eigenvector` | `Matrix.mem_range_vecMulLinear_pow_of_transpose_eigenvector` |
| `MPSTensor.fitting_nilpotent_bound` | `Matrix.fitting_nilpotent_bound` |
| `MPSTensor.fitting_nilpotent_pow_eq_zero` | `Matrix.fitting_nilpotent_pow_eq_zero` |
| `MPSTensor.WielandtRankOne.range_pow_le_iSup_maxGenEigenspace_ne_zero` | `Module.End.range_pow_le_iSup_maxGenEigenspace_ne_zero` |
| `MPSTensor.WielandtRankOne.iSup_maxGenEigenspace_ne_zero_le_range_pow` | `Module.End.iSup_maxGenEigenspace_ne_zero_le_range_pow` |
| `MPSTensor.WielandtRankOne.range_pow_eq_iSup_maxGenEigenspace_ne_zero` | `Module.End.range_pow_eq_iSup_maxGenEigenspace_ne_zero` |
| `MPSTensor.WielandtRankOne.mapsTo_range_pow` | `Module.End.mapsTo_range_pow` |
| `MPSTensor.WielandtRankOne.ker_le_maxGenEigenspace_zero` | `Module.End.ker_le_maxGenEigenspace_zero` |
| `MPSTensor.WielandtRankOne.disjoint_ker_iSup_maxGenEigenspace_ne_zero` | `Module.End.disjoint_ker_iSup_maxGenEigenspace_ne_zero` |
| `MPSTensor.WielandtRankOne.disjoint_ker_range_pow` | `Module.End.disjoint_ker_range_pow` |
| `MPSTensor.WielandtRankOne.ker_restrict_range_pow_eq_bot` | `Module.End.ker_restrict_range_pow_eq_bot` |
| `MPSTensor.WielandtRankOne.isUnit_restrict_range_pow` | `Module.End.isUnit_restrict_range_pow` |
| `MPSTensor.WielandtRankOne.isUnit_restrict_range_toLin'_pow` | `Matrix.isUnit_restrict_range_toLin'_pow` |
| `MPSTensor.WielandtRankOne.vec_eq_zero_of_mulVec_eq_zero_of_mem_range_pow` | `Matrix.vec_eq_zero_of_mulVec_eq_zero_of_mem_range_pow` |
| `MPSTensor.WielandtRankOne.matrix_eq_zero_of_mul_eq_zero_of_mem_range_mulLeft_pow` | `Matrix.eq_zero_of_mul_eq_zero_of_mem_range_mulLeft_pow` |

The generated `TNLean.MPS.Core` and `TNLean.Wielandt.RankOne` aggregators were
regenerated and no longer import the retired modules.
