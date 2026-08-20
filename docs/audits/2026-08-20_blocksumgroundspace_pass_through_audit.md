# Block-sum ground-space pass-through audit

This audit records the repository-local deprecation exception used by PR
#6824. Each declaration below was an exact pass-through with no independent
mathematical content. At the audited head, it had no non-`Archive` consumer
and no Blueprint `\lean{...}` tag.

| Removed declaration | Existing replacement |
|---|---|
| `BlockSumGroundSpace.sigmaDiagonalBlock` | the corresponding `Matrix.submatrix` compression |
| `BlockSumGroundSpace.diagonalBlock` | `Matrix.finSigmaDiagonalBlock` |
| `BlockSumGroundSpace.trace_blockDiagonal'_mul` | `Matrix.trace_blockDiagonal'_mul` |

The three declarations satisfy the exact-pass-through exception in
`docs/MATHLIB_style.md`: each only names an existing definition, theorem, or
definitional matrix compression; all non-`Archive` uses have been migrated or
were absent; and no Blueprint entry cites an old name. They are therefore
removed without deprecated compatibility declarations.
