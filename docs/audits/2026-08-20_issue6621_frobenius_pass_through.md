# Frobenius compatibility pass-through deletion audit

This cleanup uses the repository-local exact pass-through exception in
`docs/MATHLIB_style.md`.

## Removed declarations and replacements

| Removed declaration | Direct replacement |
|---|---|
| `MPSTensor.frobSq` | `Matrix.frobeniusNormSq` |
| `MPSTensor.frobSq_eq_sum` | `Matrix.frobeniusNormSq_eq_sum` |
| `MPSTensor.frobSq_trace` | `Matrix.frobeniusNormSq_eq_trace` |
| `MPSTensor.frobSq_smul` | `Matrix.frobeniusNormSq_smul` |
| `MPSTensor.matToES` | `Matrix.frobeniusEquivEuclidean` applied to the transposed matrix, which preserves the former row-column coordinate order |
| `MPSTensor.matToES_apply` | transpose vectorization through `Matrix.frobeniusEquivEuclidean_apply` |
| `MPSTensor.matToES_finset_sum` | linearity of `Matrix.frobeniusEquivEuclidean`, together with `Matrix.transpose_sum` |
| `MPSTensor.norm_matToES_sq` | `LinearIsometryEquiv.norm_map`, `Matrix.frobenius_norm_transpose`, and `Matrix.frobeniusNormSq` |
| `MPSTensor.norm_matToES_eq_frobenius_norm` | `LinearIsometryEquiv.norm_map` and `Matrix.frobenius_norm_transpose` |

Each removed declaration only forwarded the canonical Frobenius API or named the same transpose
vectorization argument. None added a hypothesis, changed a conclusion, or contained independent
mathematical content.

All non-Archive Lean consumers have been migrated to `TNLean.Algebra.FrobeniusHilbert`. Exact-name
searches found no remaining import of `TNLean.Spectral.FrobeniusNorm` and no blueprint
`\lean{...}` tag citing any removed declaration.
