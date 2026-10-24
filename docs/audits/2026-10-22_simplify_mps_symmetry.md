# Simplification pass: TNLean/MPS/Symmetry

Date: 2026-10-22. PR: #9935.

A behaviour-preserving simplification of TNLean/MPS/Symmetry. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `mulTensorAssocMatrix_eq_finCongr` | `TNLean/MPS/Symmetry/MPOSymmetry/AssociatorToolkit.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `symmetricProjection_mul` (private) | `TNLean/MPS/Symmetry/MPOSymmetry/MixedEndpointProjectorComparison.lean` | `LinearMap.IsSymmetricProjection.mul_of_commute` |
| `one_sub_mul_le_add_one_sub` (private) | `TNLean/MPS/Symmetry/MPOSymmetry/MixedEndpointProjectorComparison.lean` | `LinearMap.IsSymmetricProjection.one_sub_mul_le_add_one_sub` |
| `one_sub_mul_mul_le` (private) | `TNLean/MPS/Symmetry/MPOSymmetry/MixedEndpointProjectorComparison.lean` | `LinearMap.IsSymmetricProjection.one_sub_mul_mul_le` |
