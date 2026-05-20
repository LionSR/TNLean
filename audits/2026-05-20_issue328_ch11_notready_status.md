# Issue #328 status audit: Chapter 11 not-ready entries

Date: 2026-05-20.

This audit refreshes issue #328 against current `origin/main`
(`142d5c4930f85b31db9e47bbdf9f10018024699b`).  The issue remains useful as a
Chapter 11 status record, but several details in its body describe older
blueprint and issue states.

## Current blueprint locations

- `blueprint/src/chapter/ch11_fundamental_theorem_proof.tex` is the current
  non-periodic Chapter 11 file.  The older path
  `blueprint/src/chapter/ch11_assembly.tex` is no longer the current file.
- `blueprint/src/chapter/ch11b_periodic_ft.tex` remains the periodic
  Fundamental Theorem chapter.

## Non-periodic source statements

The non-periodic source-level entries still marked `\notready` are:

- `thm:cpgsv_multiblock_ft_source`, the multi-block fundamental theorem for
  normal tensors.
- `thm:cpgsv_equal_case_source`, the equal-case corollary.

These entries should remain `\notready`.  Existing formal statements cover
strict or conditional components of the CPSV16 route, but the source statements
as written in the blueprint still require the paper-faithful multi-copy BNT
comparison and equal-case assembly without additional hypotheses.  That work is
tracked by #1685.

The old non-periodic obstruction list in issue #328 is stale:

- #944 is closed.
- #1133 is closed.
- #1170 is closed.
- #1178 is closed.
- #1282 is closed.

Those closures do not make the two source entries ready.  They only mean that
the present obstruction is no longer the older list in issue #328, but the
source-faithful CPSV16 theorem work recorded in #1685.

## Periodic source statements

The main periodic theorem entry
`thm:periodic_ft` remains `\notready`.  Its current dependencies are:

- #81, for the periodic overlap dichotomy of arXiv:1708.00029,
  Proposition 3.3.
- #82, for the periodic Fundamental Theorem statements.
- #829, for the equal-case Z-gauge extraction and root reconstruction.

The periodic overlap family currently has these more specific open issues:

- #448, for the self-overlap limit and the remaining Cases 1--2 material.
- #450, for sector-match propagation and repeated-block assembly in Case 3.
- #1807, for the BDCF converse for orthogonal cyclic-sector traces.

The blueprint status has also changed since the body of #328 was last updated.
The entry `thm:periodic_overlap_zero_no_sector_match` is now statement-level
`\leanok`; it is no longer a `\notready` blueprint statement.  It should not be
counted among the remaining not-ready entries, although the surrounding
periodic-overlap proof family is not complete.

The same statement-level criterion applies to
`thm:periodic_self_overlap_tendsto`: the corresponding Lean declaration
exists with the stated type, so the blueprint marks the theorem `\leanok`.
Its proof still depends on the BDCF converse obligation listed below.

The following periodic entries remain `\notready` in Chapter 11b:

- `thm:periodic_ft`.
- `lem:sector_match_propagation`.
- `lem:sector_tensor_proportional_blocked_match`.
- `thm:periodic_overlap_gauge_equiv_sector_match`.
- `thm:periodic_overlap_dichotomy`.
- `thm:periodic_basis_eventually_li`.
- `rem:periodic_vs_blocking_ft`.
- `thm:peripheral_periodic_ft_proportional_same`.
- `thm:peripheral_periodic_ft_proportional_rescaling`.
- `rem:periodic_ft_proportional`.

The separate periodic-symmetry material later in Chapter 11b is tracked by
#622 and #664, not by the narrow equal-case and periodic-overlap audit in #328.

## Lean proof obligations in periodic-overlap files

The current `sorry` occurrences in the split periodic-overlap files are:

- `TNLean/MPS/Periodic/Overlap/SelfOverlap.lean:607`,
  `not_gaugePhaseEquiv_of_orthogonal_cyclicSector_traces`, tracked by #1807.
- `TNLean/MPS/Periodic/Overlap/Case2.lean:164`,
  `exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp`,
  tracked by #448.
- `TNLean/MPS/Periodic/Overlap/Case3.lean:129`,
  `sectorGaugePhaseEquiv_succ_of_cyclicTransport`, tracked by #450.
- `TNLean/MPS/Periodic/Overlap/Case3.lean:266`,
  `sectorMatch_propagation`, tracked by #450.
- `TNLean/MPS/Periodic/Overlap/Case3.lean:323`,
  `repeatedBlocks_of_blockedSectorGaugePhase`, tracked by #450.
- `TNLean/MPS/Periodic/Overlap/Case3.lean:439`,
  `periodicOverlap_gaugeEquiv_of_sector_match`, tracked by #450.
- `TNLean/MPS/Periodic/Overlap/Dichotomy.lean:58`,
  `periodicOverlapDichotomy`, tracked by #81.
- `TNLean/MPS/Periodic/Overlap/Dichotomy.lean:88`,
  `periodicBasis_eventuallyLinearlyIndependent`, tracked by #81.

Line numbers are only a snapshot.  Declaration names and tracker links are the
stable references.

## Closure recommendation for issue #328

Issue #328 can be closed after this audit is merged, provided the closure
comment records that the remaining not-ready material has moved to the current
trackers listed above.  The mathematical work is not finished; it is now recorded
more accurately by #1685 for the CPSV16 source theorem and by #81, #82, #448,
#450, #829, and #1807 for the periodic route.
