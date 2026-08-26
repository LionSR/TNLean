# MPS core, overlap, and gauge-span simplification

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for the MPS core / overlap sweep of
2026-08-26. Each declaration below either had no non-`Archive` consumer at the
audited head, or forwarded to a strictly more general sibling whose hypotheses
every call site can discharge. None carried a Blueprint `\lean{...}` tag, so no
transition declaration was left behind.

## Removed private duplicates

| Removed | Replacement |
|---|---|
| `MPSTensor.mpv_cast_dim` (private, `TNLean/MPS/CanonicalForm/Reduction.lean`) | the public `MPSTensor.mpv_cast_dim` in `TNLean/MPS/Overlap/CastLemmas.lean` |
| `MPSTensor.isIrreducibleTensor_cast` (private, `TNLean/MPS/CanonicalForm/Reduction.lean`) | the public `MPSTensor.isIrreducibleTensor_cast_dim` in `TNLean/MPS/Overlap/CastLemmas.lean` |

Both copies existed only because the cast-lemma module imported the reduction
module rather than the other way round. The import direction is now the
intended one and is recorded in
`docs/audits/2026-08-26_post_migration_spaghetti_cleanup.md` §Dependency
direction. All four call sites were in the same file and were retargeted.

## Removed zero-reference declarations

| Removed | Note |
|---|---|
| `MPSTensor.sameMPV_tpGauge` (`TNLean/MPS/Core/TPGauge.lean`) | no consumer; recover it as `GaugeEquiv.sameMPV (gaugeEquiv_tpGauge A ρ hρ)` |
| `MPSTensor.replicatedWeights_pow_ne_zero` (`TNLean/MPS/Core/BlockingInfrastructure.lean`) | no consumer; the surviving `blockWeights_ne_zero` covers the non-replicated statement |
| `MPSTensor.eq_directToIteratedBlockIndex_iff_iteratedBlockIndex_eq` (`TNLean/MPS/Core/BlockingInfrastructure.lean`) | no consumer; the two round-trip lemmas it was assembled from survive |
| `MPSTensor.mpvInner_eq_sum_of_decomp_right` (`TNLean/MPS/Overlap/Basic.lean`) | no consumer; `mpvState_eq_sum_of_decomp` above it is the live lemma |

Three files under `docs/audits/` retain historical mentions of these names
(`2026-04-27_issue971_weight_zero_tail.md`,
`2026-04-30_issue990_blocked_word_comparison.md`,
`2026-05-01_issue1077_tn_proof_tactics_scout.md`). They are dated records and
are deliberately left untouched. This sweep is an evidence update to open
ledger entry S2 (#4564), not a new debt entry.

## Retired injective-hypothesis twins

| Removed | Replacement |
|---|---|
| `MPSTensor.overlap_tendsto_one_of_peripheralPrimitive` (`TNLean/MPS/Overlap/PeripheralToTransferMapGap.lean`) | `MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible`, precomposed with `MPSTensor.irreducibleTensor_of_injective` |
| `MPSTensor.mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left` (`TNLean/MPS/Overlap/CastDecay.lean`) | `MPSTensor.mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`, precomposed with `MPSTensor.irreducibleTensor_of_injective` |

Injectivity of a matrix family implies irreducibility, so each removed twin was
the irreducible statement with a stricter hypothesis. The bridge
`MPSTensor.irreducibleTensor_of_injective`
(`TNLean/Spectral/TransferOperatorGapInjective.lean`) lost its `private`
modifier and gained a docstring so the two migrated call sites — in
`TNLean/PiAlgebra/CanonicalFormSepAux.lean` and
`TNLean/MPS/BNT/Construction.lean` — can name it.

Historical mentions of the removed names survive at
`docs/audits/2026-05-13_cpsv16_ft_paper_vs_code_structural_map.md` and
`docs/audits/2026-05-13_cpsv16_ft_definition_audit.md`; both are dated records
and are left as-is.

## Collapsed proofs

`MPSTensor.isInjective_of_gaugeEquiv` and
`MPSTensor.isNBlkInjective_of_gaugeEquiv` (`TNLean/MPS/Defs.lean`) each carried
a hand-rolled span-induction argument showing that conjugation by an invertible
matrix preserves a spanning family. QICLean already exports exactly that fact as
`Matrix.span_range_gauge_eq_top` (`QICLean/Algebra/MatrixKernelRigidity.lean`),
so both proof bodies now reduce to a generator identification plus one
application of it. Both statements, both names, and the Blueprint tag at
`blueprint/src/chapter/ch02_mps.tex` are unchanged.
