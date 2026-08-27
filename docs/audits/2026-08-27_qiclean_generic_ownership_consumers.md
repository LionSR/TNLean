# QICLean generic matrix/Kraus ownership consumer migration

Date: 2026-08-27

QICLean PR #508 (`aef0def`) established the channel-neutral owners for the
remaining low-risk generic matrix and finite-Kraus declarations identified in
the TNLean boundary audit. TNLean now pins that revision and consumes those
owners directly.

## Moved ownership

| Former TNLean location | QICLean owner | Surface |
|---|---|---|
| `TNLean/MPS/Defs.lean` | `QICLean/Kraus/Injectivity.lean` | linear-functional non-injectivity and block-non-injectivity criteria |
| `TNLean/MPS/MPU/Simple.lean` | `QICLean/Algebra/RankOneSandwich.lean` | rank-one sandwich and trace factorization for matrix lists |
| `TNLean/MPS/CanonicalForm/ProjectorClosureDecomposition.lean` | `QICLean/Algebra/OrthogonalProjection.lean` | support-isometry factorization with trace/rank equality |
| `TNLean/MPS/CanonicalForm/NormalCommutant.lean` | `QICLean/Algebra/MatrixGramConjugation.lean` and `QICLean/Kraus/NormalCommutant.lean` | Gram-conjugation algebra, normal-family commutant rigidity, and unitary normalization |

The public qualified declaration names are unchanged, so TNLean consumers now
import the QICLean owner without compatibility aliases. The obsolete
`TNLean.MPS.CanonicalForm.NormalCommutant` module is deleted rather than retained
as an import-only forwarding layer; direct MPDO consumers import
`QICLean.Kraus.NormalCommutant`.

The migration preserves the ownership boundary: MPS/MPDO statements and their
source-facing bridges remain in TNLean, while generic matrix-family and Kraus
results have a single QICLean implementation.
