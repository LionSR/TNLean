# Simplification pass: TNLean/MPS/MPU

Date: 2026-10-22. PR: #9934.

A behaviour-preserving simplification of TNLean/MPS/MPU. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `threeTupleEquiv_apply` (private) | `TNLean/MPS/MPU/AnchoredThreeBlockOperator.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `shiftSourceScale_cancel_rev` | `TNLean/MPS/MPU/Examples/ShiftSourceFactors.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `siteProduct_conjTranspose` | `TNLean/MPS/MPU/FundamentalTheoremGates.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `sourceSVD₁_V_vecMul_injective` (private) | `TNLean/MPS/MPU/SourceFactors.lean` | `MPOTensor.vecMul_injective_of_isCoisometry` |
| `isMPUSimple_virtualSandwich_gl_iff` | `TNLean/MPS/MPU/VirtualSandwichBlocking.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
