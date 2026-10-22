# Simplification pass: TNLean/MPS/Preparation and TNLean/MPS/Examples

Date: 2026-10-22. PR: #9963.

A behaviour-preserving simplification of TNLean/MPS/Preparation and TNLean/MPS/Examples. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `fibUnitAllTau_remainder_eq_zero` | `TNLean/MPS/Examples/Fibonacci/FibonacciAction.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `fibActAllTau_remainder_eq_zero` | `TNLean/MPS/Examples/Fibonacci/FibonacciAction.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `fibActChain_remainder_eq_zero` | `TNLean/MPS/Examples/Fibonacci/FibonacciAction.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `thetaTwo_eq_fromBlocks` | `TNLean/MPS/Examples/Ising/IsingGauge.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `isingSigma_apply_zero_six` | `TNLean/MPS/Examples/Ising/IsingTensors.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `siteX_mul_self` | `TNLean/MPS/Examples/KramersWannier/KramersWannierSource.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `siteZ_mul_self` | `TNLean/MPS/Examples/KramersWannier/KramersWannierSource.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `siteX_mul_siteX_comm` | `TNLean/MPS/Examples/KramersWannier/KramersWannierSource.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `siteZ_mul_siteZ_comm` | `TNLean/MPS/Examples/KramersWannier/KramersWannierSource.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `complexOfGolden_sum` | `TNLean/MPS/Examples/Rings/GoldenRing.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `complexOfGolden_single` | `TNLean/MPS/Examples/Rings/GoldenRing.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `complexOfGolden_smul` | `TNLean/MPS/Examples/Rings/GoldenRing.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `complexOfZsqrt2_single` | `TNLean/MPS/Examples/Rings/Zsqrt2Ring.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `defectEis_apply_one_zero` | `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousDefect.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `pairTarget_eq` | `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousDefectCompression.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `uMPS_apply_three` | `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousTensor.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `uMPS_apply_seven` | `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousTensor.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `uMPS_apply_two` | `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousTensor.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `mpvExpectation_add` | `TNLean/MPS/Preparation/DepthLowerBoundCore.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `conjTranspose_physicalMatrix_approximatingTensor_mul_blocked` | `TNLean/MPS/Preparation/OrthogonalBlockSum.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `posSemidef_embeddedBlockState` (private) | `TNLean/MPS/Preparation/OverlappingBlockOverlap.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
