# Simplification pass: the TNLean/PEPS root files A–R

Date: 2026-10-22. PR: #9968.

A behaviour-preserving simplification of the TNLean/PEPS root files A–R. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `Edge.ofAdj_symm` | `TNLean/PEPS/Defs.lean` | `Edge.ofAdj_of_lt` or `Edge.ofAdj_of_gt`, for the required orientation |
