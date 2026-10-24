# Simplification pass: the core MPS directories

Date: 2026-10-22. PR: #9932.

A behaviour-preserving simplification of the core MPS directories. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `leftSectorTensor_supported` | `TNLean/MPS/CanonicalForm/CyclicSectors/Basic.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `assocInv_mul_kronId_kronId_assoc` | `TNLean/MPS/Core/ReductionComposition.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `assocInv_pentagon_assoc` | `TNLean/MPS/Core/ReductionComposition.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `directSum_z` | `TNLean/MPS/FundamentalTheorem/Reduction/MultiBlockDirectSum.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `WordModule.toVec` | `TNLean/MPS/FundamentalTheorem/Reduction/WordModule.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
