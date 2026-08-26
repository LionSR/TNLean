# Mixed-map compatibility aliases: intentional retirement

Date: 2026-08-26

## Decision

PR #7192 migrated TNLean from the retired `mixedTransferMap` and `mixedTransferMap₂` vocabulary to
the canonical QICLean API `Kraus.mixedMapLM`. No deprecated aliases are provided for the renamed
TNLean declarations listed below.

This is a deliberate architectural exception to the usual mathematical-language rename rule in
`docs/CONTRIBUTING.md`. The change was not an isolated spelling improvement: QICLean PR #504
deleted the entire `QICLean.Spectral.MixedTransfer` compatibility module, and TNLean PR #7192
removed its final downstream theorem ecosystem. Reintroducing the old declaration names would
recreate the compatibility surface that the ownership migration intentionally retired.

`Kraus.mixedMapLM` is now the sole generic mixed-map API. Tensor-network statements may retain
mixed-transfer terminology in prose, but declaration names should identify the canonical map they
use. The exact MPS-domain abbreviation `Kraus.transferMap` remains a separate, explicitly retained
exception and does not justify rebuilding the deleted mixed-map aliases.

## Rename inventory

| Retired declaration name | Canonical declaration name |
|---|---|
| `MPSTensor.mixedTransferMap₂_rotatePhysical` | `MPSTensor.mixedMapLM_rotatePhysical` |
| `MPSTensor.mixedTransferMap₂_comp_self_eq_smul_of_transferMap_comp_self_eq_smul` | `MPSTensor.mixedMapLM_comp_self_eq_smul_of_transferMap_comp_self_eq_smul` |
| `MPSTensor.mixedTransferMap₂_isIdempotentElem_of_isTransferIdempotent_directSum` | `MPSTensor.mixedMapLM_isIdempotentElem_of_isTransferIdempotent_directSum` |
| `MPSTensor.blockTransferSum_idempotent_of_pairwise_mixedTransferMap₂` | `MPSTensor.blockTransferSum_idempotent_of_pairwise_mixedMapLM` |
| `MPSTensor.isTransferIdempotent_directSumTensor_iff_pairwise_mixedTransferMap₂_isIdempotentElem` | `MPSTensor.isTransferIdempotent_directSumTensor_iff_pairwise_mixedMapLM_isIdempotentElem` |
| `MPSTensor.normalizedMinimalLoopTensor_mixedTransferMap₂_eq_zero_of_ne` | `MPSTensor.normalizedMinimalLoopTensor_mixedMapLM_eq_zero_of_ne` |
| `MPSTensor.mixedTransferMap₂_conj_apply` | `MPSTensor.mixedMapLM_conj_apply` |
| `MPSTensor.mixedTransferMap₂_eq_zero_of_conj` | `MPSTensor.mixedMapLM_eq_zero_of_conj` |
| `MPSTensor.mixedTransferMap₂_eq_zero_of_gaugePhaseEquiv` | `MPSTensor.mixedMapLM_eq_zero_of_gaugePhaseEquiv` |
| `MPSTensor.mixedTransferMap₂_cast_eq_zero_iff` | `MPSTensor.mixedMapLM_cast_eq_zero_iff` |
| `MPSTensor.residual_isometry_entry_of_mixedTransferMap₂_eq_zero` | `MPSTensor.residual_isometry_entry_of_mixedMapLM_eq_zero` |
| `MPSTensor.trace_mixedTransferMap_pow_eq_mpvOverlap` | `MPSTensor.trace_mixedMapLM_pow_eq_mpvOverlap` |
| `MPSTensor.trace_transferMatrix_mixedTransferMap_pow_eq_mpvOverlap` | `MPSTensor.trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap` |
| `MPSTensor.trace_mixedTransferMap₂_pow_eq_mpvOverlap` | `MPSTensor.trace_mixedMapLM_rect_pow_eq_mpvOverlap` |

The post-migration cleanup report is
`docs/audits/2026-08-26_post_migration_spaghetti_cleanup.md`.
