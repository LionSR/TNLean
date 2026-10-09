# Rename of the rectangular bound on the norm of `1 ⊗ B`

QICLean `eb12c672` (QICLean #665) added the theorem
`Matrix.l2_opNorm_one_kronecker_le` in `QICLean/Analysis/TraceMulBound.lean`,
which states `‖1 ⊗ G‖ ≤ ‖G‖` for a square complex matrix `G`.
`TNLean/Algebra/MatrixKroneckerContraction.lean` declared a theorem with the same
fully qualified name stating the inequality for a rectangular matrix `B`, so the
two libraries could not be imported together after the QICLean pin bump.

The TNLean statement is the more general one, and `Matrix.l2_opNorm_kronecker_le`
uses it with a rectangular factor, so it is kept under a new name.

## Removed declaration and its replacement

| Removed declaration | Replacement |
|---|---|
| `Matrix.l2_opNorm_one_kronecker_le` (TNLean, rectangular) | `Matrix.l2_opNorm_one_kronecker_rect_le`, same statement and proof |

The old fully qualified name now resolves only to QICLean's square theorem.
The three uses, in `TNLean/Algebra/MatrixKroneckerContraction.lean`,
`TNLean/PEPS/Approximation/TwoSheetExchange.lean` and
`TNLean/PEPS/Approximation/SheetSwapCorrection.lean`, now cite the new name. No
blueprint `\lean{...}` tag cites the old name, and no other use exists in
`TNLean`, `blueprint`, `docs` or `scripts`.
