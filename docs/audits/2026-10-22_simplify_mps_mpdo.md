# Simplification pass: TNLean/MPS/MPDO

Date: 2026-10-22. PR: #9933.

A behaviour-preserving simplification of TNLean/MPS/MPDO. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `ofWords_left` | `TNLean/MPS/MPDO/CompleteZipperFusionBlocked.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `ofWords_right` | `TNLean/MPS/MPDO/CompleteZipperFusionBlocked.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `leftTreeGaugeInv_mul_leftTreeGauge` | `TNLean/MPS/MPDO/CompleteZipperFusionGauge.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `mulTensor_smul_left` | `TNLean/MPS/MPDO/OperatorProduct.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `mulTensor_smul_right` | `TNLean/MPS/MPDO/OperatorProduct.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `activeRestrictedPhysicalSectorFactorization_sector` | `TNLean/MPS/MPDO/PhysicalSectorActiveNeighboring.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `closedSectorTraceMatrix_normalized_trace_pow_eq_trace` | `TNLean/MPS/MPDO/SectorPairingTransfer.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
