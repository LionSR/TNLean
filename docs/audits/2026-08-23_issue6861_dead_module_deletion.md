# Issue 6861: compatibility retirement audit

This note records the compatibility decision for two TNLean-local modules from
the August 2026 mass-deletion review. The audit was repeated at the branch
point from `main`: none of the names below has a non-`Archive` Lean consumer,
and no Blueprint `\lean{...}` tag names one of them.

Repository-wide prose search finds only dated inventory snapshots in
`docs/audits/`. These records describe earlier tree states; they neither
prescribe an import nor present either module as a current public interface.

## Retained: `TNLean/MPS/Core/BlockTriangularTrace.lean`

The module is reachable through the generated `TNLean.MPS.Core` aggregator. It
contains the following substantive public declarations:

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

Issue #7135 completed the compatibility transition. The implementation now
uses the orthogonal projection obtained by reindexing
`Matrix.fromBlocks 1 0 0 0` along `finSumFinEquiv`; its complement is
`Matrix.fromBlocks 0 0 0 1`. The exact replacement relation is:

| Retained coordinate declaration | Projection-based implementation |
|---|---|
| `MPSTensor.upperSum` | Definition `fun i ↦ Matrix.fromBlocks (A11 i) (A12 i) 0 (A22 i)` |
| `MPSTensor.diagSum` | Definition `fun i ↦ Matrix.fromBlocks (A11 i) 0 0 (A22 i)` |
| `MPSTensor.upperFin` | `upperSum` reindexed along `finSumFinEquiv` |
| `MPSTensor.diagFin` | The same reindexing of `diagSum`; the bridge proves it is `Kraus.diagPart upperFin coordProj` |
| `MPSTensor.trace_fromBlocks_upper` | `Matrix.trace_eq_trace_diag_of_proj` plus the two block-compression identities |
| `MPSTensor.evalWord_upperSum_is_fromBlocks` | `Kraus.lowerZero_evalWord` and `Kraus.evalWord_diagPart_eq`, transported through `finSumFinEquiv` |
| `MPSTensor.evalWord_diagSum_is_fromBlocks` | The two diagonal inclusion intertwiners, via `Kraus.evalWord_intertwine` |
| `MPSTensor.trace_evalWord_upperSum_eq_trace_evalWord_diagSum` | `Kraus.trace_evalWord_diagPart_eq` plus the `diagPart_upperFin` and trace-reindex bridges |
| `MPSTensor.mpv_upperFin_eq_mpv_diagFin` | Pointwise specialization of `MPSTensor.sameMPV_diagPart_of_lowerZero` through `diagPart_upperFin` |
| `MPSTensor.sameMPV_upperFin_diagFin` | Direct specialization of `MPSTensor.sameMPV_diagPart_of_lowerZero` through `diagPart_upperFin` |

Thus no independent word induction remains in the coordinate module, and the
coordinate names are compatibility wrappers around the projection argument.
They remain available; deletion and deprecation are outside #7135.

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

The generated `TNLean.Algebra` and `TNLean.Wielandt.RankOne` aggregators were
regenerated. The former continues to import `BlockTriangularTrace`; the latter
no longer imports `MatrixFittingRange`.
