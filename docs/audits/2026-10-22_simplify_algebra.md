# Simplification pass: TNLean/Algebra

Date: 2026-10-22. PR: #9924.

A behaviour-preserving simplification of TNLean/Algebra. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `blockProj_apply_of_fst_ne` | `TNLean/Algebra/BlockTriangularWord.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `half_le_floor_of_one_le` | `TNLean/Algebra/ExplicitThresholds.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `pow_sub_pow_eq_sum_mul_sub_mul` | `TNLean/Algebra/NormedRingTelescoping.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `oneMagnon_ne_zero` | `TNLean/Algebra/OneMagnon.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `ofWord_eq_single` | `TNLean/Algebra/WordAlgebra.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `aug_ofWord_of_ne_nil` | `TNLean/Algebra/WordAlgebra.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
