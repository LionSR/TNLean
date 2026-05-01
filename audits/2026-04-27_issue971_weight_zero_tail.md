# 2026-04-27 — Issue #971 weight transport and zero-tail reblocking

This branch adds checked auxiliary identities for transporting nonzero-block weights and zero-tail MPV identities through positive physical reblocking, as a modular input for the common cyclic-sector flattening work in #969.

## Lean declarations added

In `TNLean/MPS/Core/BlockingInfrastructure.lean`:

- `MPSTensor.blockedFlatConfig` and `MPSTensor.mpv_blockTensor_eq_mpv_blockedFlatConfig`: shared flattened-configuration helpers for reusing the same original physical word across blocked tensors.
- `MPSTensor.sameMPV₂_blockTensor_toTensorFromBlocks`: direct adapter saying that blocking an assembled weighted block tensor agrees, as an MPV family, with assembling the individually blocked blocks and powered weights.
- `MPSTensor.sameMPV₂Pos_blockTensor`: positive-length MPV equality is preserved by positive blocking.
- `MPSTensor.sameMPV₂Pos_toTensorFromBlocks_blockPower`: positive-length equality of two weighted nonzero-block tensors is preserved by positive common blocking, with weights transported to powers.
- `MPSTensor.blockWeights_ne_zero`: nonzero block weights remain nonzero after blocking powers.
- `MPSTensor.replicatedWeights_pow_ne_zero`: nonzero block weights remain nonzero when replicated over cyclic sectors with per-block powers.
- `MPSTensor.replicatedWeights_pow_mul_phase_ne_zero`: the same nonvanishing persists after multiplying by nonzero sector phase factors.

In `TNLean/MPS/CanonicalForm/Assembly/TPPrimitiveReduction.lean`:

- `MPSTensor.zeroTail_mpv_decomp_blockTensor`: a zero-tail/live MPV decomposition remains a zero-tail/live decomposition after positive blocking, with the zero-tail term still isolated at blocked length zero.
- `MPSTensor.zeroTail_toTensorFromBlocks_blockPower`: the weighted-live version, transporting `μ_k` to `μ_k^p` and `B_k` to `B_k^[p]`.

In `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean`:

- `MPSTensor.liveBlock_blockPower_positive_sameMPV₂_and_zeroTail_bookkeeping_of_sameMPV₂`: combines the reblocked zero-tail identities for two globally equal MPV families to give positive-length equality of powered nonzero-block tensors plus the exact blocked length-zero zero-tail identity.

## Refactor

`MPSTensor.exists_tp_primitive_blockDecomp_after_blocking` now uses `blockWeights_ne_zero` and `zeroTail_toTensorFromBlocks_blockPower` instead of reproving the power and length-zero arithmetic inline.

## Remaining #969/#971 interface gap

These lemmas do not yet construct the final flattened cyclic-sector family at one common physical blocking level. They provide the reusable arithmetic and MPV bookkeeping that such a theorem should call once the dependent-index flattening and nested-blocking associativity data are fixed.

## 2026-05-01 update — coordinate-grouped common-sector transport

After the common-sector comparison and blocked-word grouping infrastructure
merged, the one-sided zero-tail transport can be stated directly from the precise
coordinate assertion now isolated in
`CommonBlockedCyclicSectorFamily.groupedBlockCastAgrees`.

New declarations in `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean`:

- `MPSTensor.zeroTail_commonFlatAt_of_groupedBlockCastAgrees`: the grouped-block
  comparison rewrites the zero-tail equation with the weighted common-sector
  family at any prescribed equal common length.
- `MPSTensor.sameMPV₂Pos_blockTensor_commonFlatAt_of_groupedBlockCastAgrees`: at
  positive lengths the zero-tail term vanishes, so the blocked tensor agrees with
  that weighted common-sector family.
- `MPSTensor.zeroTail_commonFlat_transport_of_groupedBlockCastAgrees`: bundles the
  zero-tail equation, the weighted nonzero-part MPV equality, and nonvanishing of
  the transported common-sector weights under the grouped-block coordinate
  assertion.
- `MPSTensor.CommonGroupedBlockCastHypothesis` and
  `MPSTensor.CommonGroupedBlockCastHypothesis.toRelabelingHypothesis`: record the
  global coordinate-grouping assertion and show that it implies the reindexed
  nonzero-part hypothesis used by the common-sector structural theorem.

This does not prove the coordinate assertion itself.  After #1096, the direct
and iterated blocked alphabets are related by the explicit equivalence
`directIteratedBlockEquiv`, and
`groupedBlockCastAgrees_iff_iteratedBlockIndex_cast` restates the remaining point
as the comparison between this equivalence and the canonical identification used
inside `CommonBlockedCyclicSectorFamily`.  The present transport theorem therefore
uses the grouped-block coordinate assertion as the honest remaining input rather
than replacing it by a stronger unproved coordinate choice.
