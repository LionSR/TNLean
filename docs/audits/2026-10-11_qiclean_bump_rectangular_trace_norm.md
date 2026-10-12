# QICLean bump to 3b93ddff: rectangular trace norm truncation

Date: 2026-10-11. PR: chore(deps): bump QICLean to the rectangular trace norm
truncation and drop the local nuclear-norm module.

LionSR/QICLean#781 adds `QICLean/Analysis/RectangularTraceNormTruncation.lean`,
which states the estimates of `TNLean/Algebra/NuclearNormTruncation.lean` for
QICLean's `Matrix.rectangularTraceNorm`. Most declarations have the same fully
qualified name in both libraries, so keeping the TNLean module would make the
root module fail to load once the bumped QICLean is imported. The module is
deleted, and no deprecated aliases are kept.

## Removed declarations and replacements

`Matrix.nuclearNorm` and `Matrix.rectangularTraceNorm` have the same definition,
the sum of the singular values of `toEuclideanLin M`.

| Removed (TNLean) | Replacement (QICLean `3b93ddff`) |
|---|---|
| `Matrix.nuclearNorm` | `Matrix.rectangularTraceNorm` |
| `Matrix.nuclearNorm_nonneg` | `Matrix.rectangularTraceNorm_nonneg` |
| `Matrix.nuclearNorm_eq_sum_range` | `Matrix.rectangularTraceNorm_eq_sum_fin` (sum over `Fin (card β)`) |
| `Matrix.nuclearNorm_eq_sum_norm` | `Matrix.rectangularTraceNorm_eq_sum_norm` |
| `Matrix.nuclearNorm_mul_transpose_le` | `Matrix.rectangularTraceNorm_mul_transpose_le` |
| `Matrix.singularValues_eq_norm` | `Matrix.singularValues_toEuclideanLin_eq_norm` |
| `Matrix.frobenius_norm_sq_eq_sum` | same name in QICLean |
| `Matrix.frobenius_norm_submatrix_equiv` | same name in QICLean |
| `Matrix.ofLp_toEuclideanLin_apply` | same name in QICLean |
| `Matrix.sum_norm_sq_toEuclideanLin_le` | same name in QICLean |
| `Matrix.sum_norm_sq_toEuclideanLin_basis` | same name in QICLean |
| `Matrix.rightSingularBasis` | same name in QICLean |
| `Matrix.inner_toEuclideanLin_rightSingularBasis` | same name in QICLean |
| `Matrix.norm_sq_toEuclideanLin_rightSingularBasis` | same name in QICLean |
| `Matrix.orthonormalProjector` | same name in QICLean |
| `Matrix.toEuclideanLin_orthonormalProjector` | same name in QICLean |
| `Matrix.exists_orthonormal_truncation` | same name in QICLean |
| `WholeGroup.conjTranspose_orthonormalProjector` (`GroupTruncation.lean`) | `Matrix.conjTranspose_orthonormalProjector` |
| `WholeGroup.orthonormalProjector_mul_self` (`GroupTruncation.lean`) | `Matrix.orthonormalProjector_mul_self` |

## Renamed TNLean theorems

The statements are unchanged except that `Matrix.nuclearNorm` is now spelled
`Matrix.rectangularTraceNorm`.

| Old name | New name |
|---|---|
| `WholeGroup.nuclearNorm_flattening_le_one` | `WholeGroup.rectangularTraceNorm_flattening_le_one` |
| `WholeGroup.nuclearNorm_flattening_network_le_one` | `WholeGroup.rectangularTraceNorm_flattening_network_le_one` |
| `WholeGroup.nuclearNorm_groupFlattening_contraction_le_one` | `WholeGroup.rectangularTraceNorm_groupFlattening_contraction_le_one` |

No open pull request used any of the removed or renamed names when this PR was
opened. The blueprint tags in `ch24_peps_group_truncation.tex` were repointed.
