# Issue #6855: core compatibility thinning audit

This note records the first TNLean-local reduction of the duplicate
`Kraus`/`MPSTensor` and bond-cast interfaces from the August 2026 structural
debt review.

## Blocking definitions

The following public `MPSTensor` names remain available, but their copied
definition bodies are replaced by abbreviations of the canonical QICLean
finite-family definitions:

| TNLean name | Canonical body |
|---|---|
| `MPSTensor.blockPhysDim` | `Kraus.blockPhysDim` |
| `MPSTensor.singleBlockEquiv` | `Kraus.singleBlockEquiv` |
| `MPSTensor.decodeBlock` | `Kraus.decodeBlock` |
| `MPSTensor.wordOfBlock` | `Kraus.wordOfBlock` |
| `MPSTensor.decodeBlockEquiv` | `Kraus.decodeBlockEquiv` |
| `MPSTensor.blockTensor` | `Kraus.blockTensor` |
| `MPSTensor.flattenBlockedWord` | `Kraus.flattenBlockedWord` |

The forwarding lemmas retain their TNLean names for compatibility, while only
the canonical `Kraus` copies carry the simplification attributes.  The three
injectivity-predicate copies named by issue #6855 no longer occur on current
main: the QICLean extraction removed their former TNLean module and migrated
live consumers directly to the canonical predicates.

## Bond reindexing

`MPSTensor.reindex` is now the canonical equivalence for transport along an
equality of bond dimensions.  Its application, word-evaluation, MPV, and gauge
lemmas replace four private cast calculations:

| Removed private declaration | Replacement |
|---|---|
| `MPSTensor.CPSVCanonicalFormData.mpsTensor_cast_apply` in `CanonicalFormEqualAmbient.lean` | `MPSTensor.cast_eq_reindex` and `MPSTensor.reindex_apply_eq_cast` |
| `MPSTensor.mpsTensor_cast_apply` in `FundamentalCoord.lean` | `MPSTensor.cast_eq_reindex` and `MPSTensor.reindex_apply_apply` |
| `MPSTensor.mpsTensor_cast_apply_matrix` in `PreparedReconstruction.lean` | `MPSTensor.cast_eq_reindex` and `MPSTensor.reindex_apply_eq_cast` |
| `MPOTensor.RetainedProductSpectralFamily.castTensor_apply` in `VerticalProductCornerComparison.lean` | `MPSTensor.cast_eq_reindex` and `MPSTensor.reindex_apply_eq_cast` |

The remaining differently named cast helpers in
`NormalizedGroupedSectorMaps.lean` and
`BNTAlgebraTensorClauseDirectSumUnitary.lean` have different dependent
contexts and are not claimed by this first migration.

## Grouped normalization and coordinate cleanup

The module `TNLean/MPS/MPDO/CPSVGroupedGramNormalization.lean` has been
deleted.  Its two public declarations,
`MPSTensor.IsCPSVCanonicalForm.grouped_sector_gram_eq_pos_smul_one` and
`MPSTensor.IsCPSVCanonicalForm.grouped_sector_exists_unitary_normalization`,
remain under the same names and with the same source-facing signatures in
`GroupedGramNormalization.lean`.  Their proofs now pass through the common
`MPOTensor.VerticalBNTGrouping` package shared with the horizontal case.

The private, zero-consumer theorem `localConfig_value_eq_left` was also
removed from `PEPS/FundamentalTheorem/GaugeAction.lean`.  The surviving gauge
proofs use the endpoint-specific `localOfDoubled` coordinate equations
directly, so retaining this separate consistency projection would add a dead
declaration rather than a reusable interface.

## MPV and mixed transfer

`SameMPV` remains a public name, now as the equal-bond-dimension abbreviation
of `SameMPV₂`.  `SameMPV₂Pos` remains distinct because its positive-length
condition records genuine mathematical information at chain length zero.

The duplicated mixed-transfer definitions and same-dimension bridge are owned
by the pinned QICLean dependency, not by TNLean.  All TNLean consumers of
`Kraus.mixedTransferMap₂_same_dim` have been rewritten by definitional
equality.  QICLean still has its own consumers of that bridge, so deletion of
the bridge and mixed-transfer suite requires an upstream refactor rather than a
TNLean compatibility copy.

## Trace-preserving and unital predicates

TNLean now uses `Kraus.IsTP` and `Kraus.IsUnital` at every former local use of
the same-type `IsTPKraus` and `IsUnitalKraus` spellings.  The five proofs that
construct `IsTracePreservingMap` for a transfer map pass through the canonical
QICLean theorem for `Kraus.mapLM` and then rewrite by
`Kraus.mapLM_eq_transferMap`.

The two copied predicate definitions themselves remain in the pinned QICLean
revision, so they cannot be changed in this repository.  QICLean exposes the
forward implication from `Kraus.IsTP` to trace preservation of `Kraus.mapLM`;
the reverse implication follows from its generic trace-adjoint results, but no
canonical specialized iff theorem is presently named.  Consolidating that API
belongs upstream.  No TNLean compatibility copy is added to conceal the
ownership boundary.
