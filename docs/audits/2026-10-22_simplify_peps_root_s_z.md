# Simplification pass: the TNLean/PEPS root files S–Z

Date: 2026-10-22. PR: #9967.

A behaviour-preserving simplification of the TNLean/PEPS root files S–Z. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `boundary_snd_notMem` | `TNLean/PEPS/TorusAbsorbedCovariance.lean` | `TNLean.PEPS.boundary_right_not_mem` |
| `mem_endPair_of_mem_leftWindow` (private) | `TNLean/PEPS/TorusWindowExtraction.lean` | `horizontalStaircaseLeftWindow_subset_endPair` |
| `mem_endPair_of_mem_rightWindow` (private) | `TNLean/PEPS/TorusWindowExtraction.lean` | `horizontalStaircaseRightWindow_subset_endPair` |
