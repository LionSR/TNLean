# Simplification pass: TNLean/MPS/ParentHamiltonian

Date: 2026-10-22. PR: #9931.

A behaviour-preserving simplification of TNLean/MPS/ParentHamiltonian. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `continuous_localTermES_family` | `TNLean/MPS/ParentHamiltonian/GroundSpaceMapContinuity.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
