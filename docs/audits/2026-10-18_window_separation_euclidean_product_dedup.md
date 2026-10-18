# Euclidean action of a matrix product in the window separation

This note records a public theorem removed from the shallow-circuit preparation development.
It is the audit note required by `docs/project_conventions.md` §Style. Both uses outside
`Archive` now cite the shared lemma, no blueprint `\lean{...}` tag cites the removed name,
and no compatibility alias is kept.

## Removed declarations

| Removed | Replacement |
|---|---|
| `MPSPreparation.toEuclideanLin_mul_apply` (module `TNLean.MPS.Preparation.WindowSeparation`) | `Matrix.toEuclideanLin_mul_apply` (module `TNLean.Algebra.ToEuclideanLinApply`) |

Both state that for square complex matrices `X` and `Y` and a vector `v` of the Euclidean space,
the matrix `X * Y` acts on `v` as `X` applied after `Y`. The replacement has the same
hypotheses and conclusion. The two call sites, in `WindowSeparation.lean` and
`BlockVariance.lean`, now cite `Matrix.toEuclideanLin_mul_apply`.
