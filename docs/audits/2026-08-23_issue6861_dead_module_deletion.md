# Issue 6861: dead-module deletion audit

This note records the first TNLean-local orphan-module deletion from the
August 2026 mass-deletion review. The audit was repeated at the branch point
from `main`: none of the names below has a non-`Archive` Lean consumer, and no
Blueprint `\lean{...}` tag names one of them.

## `TNLean/Algebra/BlockTriangularTrace.lean`

The whole module was reachable only through the generated `TNLean.Algebra`
aggregator. The following declarations are removed without replacements:

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

These declarations formed one abandoned upper-triangular reduction route. No
retained theorem depends on the route, so introducing a replacement wrapper
would preserve the dead layer rather than preserve a public mathematical API.

## `TNLean/Wielandt/RankOne/MatrixFittingRange.lean`

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

The generated `TNLean.Algebra` and `TNLean.Wielandt.RankOne` aggregators were
regenerated after both files were removed.
