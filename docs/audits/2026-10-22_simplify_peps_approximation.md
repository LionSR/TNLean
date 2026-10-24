# Simplification pass: TNLean/PEPS/Approximation

Date: 2026-10-22. PR: #9964.

A behaviour-preserving simplification of TNLean/PEPS/Approximation. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `translate_scale` | `TNLean/PEPS/Approximation/AdaptivePatchSupply.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `translate_dim` | `TNLean/PEPS/Approximation/AdaptivePatchSupply.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `translate_outer` | `TNLean/PEPS/Approximation/AdaptivePatchSupply.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `exists_const_mul_rpow_le_rpow` | `TNLean/PEPS/Approximation/CellTwoFamilyPartition.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |

The four elementary helpers `tile_subset_box`, `dyadicAnchor_ne_zero`, `holeRadius_nonneg` and
`edgeOperations_eq_append`, which this pass also found unused, were removed first by #9889 and are
recorded in `docs/audits/2026-10-22_peps_approximation_elementary_deletions.md`.
