# MPDO trace-preserving spin reduction alias deletion

Date: 2026-10-12. PR: refactor(MPS/MPDO): remove the trace-preserving spin
reduction alias. Issue: #7912 (item 6 of the round-two architectural
simplification survey, candidate E20).

## Removed declarations

* `MPOTensor.HasTracePreservingSpinReduction` (`TNLean/MPS/MPDO/PRFP.lean`).
  Replacement: `IsKrausCPTP (MPOTensor.ancillaryTraceMap d dK)`, which was its
  body.
* `MPOTensor.hasTracePreservingSpinReduction` (same file). Replacement:
  `MPOTensor.ancillaryTraceMap_isKrausCPTP` in the same file, which has the
  same statement after unfolding the definition above and was its body.

Neither name had a Lean consumer. No deprecated alias is kept.

## Blueprint deletions

`def:mpdo_has_trace_preserving_spin_reduction` and
`cor:mpdo_has_trace_preserving_spin_reduction`
(`blueprint/src/chapter/ch21_mpdo_rfp_foundations.tex`) were deleted with the
corollary's proof environment. Only the corollary referred to the definition,
and no other `\uses` or `\ref` named either label. The citation of
arXiv:1606.00608, lines 761--764, moved into the statement of
`thm:mpdo_ancillary_trace_map_is_kraus_cptp`, which is tagged with
`MPOTensor.ancillaryTraceMap_isKrausCPTP` and states the same result for every
ancillary dimension.

## Supersedes

`docs/audits/2026-08-26_mpdo_prfp_alias_and_percopy_horizontal_cf_deletion.md`
kept `MPOTensor.hasTracePreservingSpinReduction` because it was the only
declaration tagged at `cor:mpdo_has_trace_preserving_spin_reduction`. With the
source citation moved to the theorem node of the ancillary trace, that tag is
no longer needed. The same note's retention of `MPOTensor.HorizontalCFData` and
`MPOTensor.blockwise_insert_eq_of_mpv_agree` still stands: the structure is
consumed under `TNLean/MPS/MPDO/BiCFDerivation/`, and the theorem is tagged at
`lem:blockwise_insert_eq_of_mpv_agree` and cited by
`docs/paper-gaps/cpgsv17_bicf_block_separation.tex`.
