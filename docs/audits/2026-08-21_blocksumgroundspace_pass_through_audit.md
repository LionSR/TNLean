# BlockSumGroundSpace pass-through audit

This audit records the repository-local deprecation exception used by PR #6824.
Each declaration below was an exact pass-through with no independent
mathematical content. At the audited head, it had no non-`Archive` consumer
outside `TNLean/MPS/ParentHamiltonian/BlockSumGroundSpace.lean` itself and no
Blueprint `\lean{...}` tag.

| Removed declaration | Existing replacement |
|---|---|
| `BlockSumGroundSpace.sigmaDiagonalBlock` | `Matrix.finSigmaDiagonalBlock` after `Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv`; the extraction body is identical |
| `BlockSumGroundSpace.diagonalBlock` | `Matrix.finSigmaDiagonalBlock` (`TNLean/MPS/SharedInfra/BoundaryDecomposition.lean`); the bodies are definitionally equal, bridged by `rfl` before this removal |
| `BlockSumGroundSpace.trace_blockDiagonal'_mul` | `Matrix.trace_blockDiagonal'_mul` (`TNLean/Algebra/DependentBlockDiagonal.lean`); the removed theorem was a `simpa` pass-through |

All call sites inside `BlockSumGroundSpace.lean` were rewritten to use
`Matrix.finSigmaDiagonalBlock` directly. No other public declaration was
removed by this wave.
