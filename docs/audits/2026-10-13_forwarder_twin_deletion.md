# Forwarder twin deletion

Date: 2026-10-13. PR: refactor: delete forwarder twins and retag their
blueprint nodes. Issue: #7912 (items 1--5 and 7--10 of the round-two
architectural simplification survey, candidate E20; item 6 was handled in
`docs/audits/2026-10-12_mpdo_trace_preserving_spin_reduction_alias.md`).

Each removed declaration restated another declaration, with the same
conclusion and the same or stronger hypotheses, and had at most one Lean
consumer. No theorem statement of a surviving declaration changed, and no
deprecated alias is kept.

## Removed declarations and replacements

Each entry gives the issue item, the removed declaration, its file, and the
replacement.

1. `MPSTensor.pairIdentity_mem_pairWordTupleSpan_eventually_of_pairAllWordsSpanTop_period_window`
   (`TNLean/MPS/MPDO/BiCFDerivation/PairHomogenization/Span.lean`). Replacement:
   `MPSTensor.pairIdentity_mem_pairWordTupleSpan_eventually_of_pairWordTupleSpanTop_period_window`,
   which drops the unused all-words span hypothesis.
2. `TNLean.PEPS.localGauge_exists`
   (`TNLean/PEPS/FundamentalTheorem/LocalGaugeExtraction.lean`). Replacement:
   `TNLean.PEPS.localGauge_exists_of_factorizedLocalGauge`, the same statement.
3. `TNLean.PEPS.regionUnionPart_inside_disjoint_three`
   (`TNLean/PEPS/InjectiveRegion.lean`). Replacement:
   `TNLean.PEPS.regionInside_disjoint_outside`, the same statement after
   unfolding the indexed parts.
4. `MPSTensor.wolf_theorem_6_8_kraus_span`
   (`TNLean/Wielandt/Primitivity/Equivalence.lean`). Replacement:
   `MPSTensor.primitivePaper_iff_hasEventuallyFullKrausRank`, the same
   statement; its docstring now names Wolf Theorem 6.8.
5. `MPSTensor.gauge_unique_up_to_scalar_of_sameMPV`
   (`TNLean/MPS/Symmetry/GaugeUniqueness.lean`). Replacement:
   `MPSTensor.gauge_unique_up_to_scalar`, which drops the unused equal-MPV
   hypothesis.
7. `TNLean.PEPS.IsVertexInjective.edgeBlockedEndpointTensorMaps_injective_all`
   (`TNLean/PEPS/EdgeMiddlePhysical/Basic.lean`). Replacement:
   `TNLean.PEPS.IsVertexInjective.edgeBlockedEndpointTensorMaps_injective`, the
   same assertion with the edge as an explicit argument.
8. `MPOTensor.CZX.tensor_eq_blockTensor` (`TNLean/MPS/MPDO/CZXTensor.lean`).
   Replacement: `MPOTensor.blockTwo_eq_blockTensor_reindex` applied to
   `MPOTensor.CZX.decoratedSiteTensor`.
9. `TNLean.PEPS.hasFactorizedLocalGauge_of_blockedMiddleGaugeFormula`
   (`TNLean/PEPS/LocalGauge.lean`). Replacement:
   `TNLean.PEPS.hasFactorizedLocalGauge_of_localGaugeFormula`, the same
   statement, since `BlockedMiddleGaugeFormula` abbreviates its hypothesis.
10. The private `subalgebra_prod_eq_top_of_axes`
    (`TNLean/MPS/MPDO/BiCFDerivation/PairHomogenization/Algebra.lean`) was
    inlined into `MPSTensor.matrixPairSubalgebra_eq_top_of_axes`, its only use.

The only Lean call site, in `TNLean.PEPS.localGauge_exists_of_blockedMiddleGaugeFormula`,
now applies `hasFactorizedLocalGauge_of_localGaugeFormula`; the docstrings that
named items 2 and 9 now name the replacement.

## Blueprint changes

* Items 1, 2 and 3: the deleted name was dropped from a node that already
  tags its replacement (`ch13_parent_hamiltonian_block_intersections.tex`,
  `thm:localGauge_exists`, `lem:peps_regionUnionDecomposition_disjoint`).
* Item 4: `thm:wolf_6_8_kraus_span` is now tagged with
  `MPSTensor.primitivePaper_iff_hasEventuallyFullKrausRank`, whose statement is
  the node's statement. The tag moved from `thm:wielandt_proposition_three`,
  which keeps the two equivalences with strong irreducibility; together these
  give its three-way equivalence. Each declaration still has one owning node.
* Item 9: `thm:peps_hasFactorizedLocalGauge_of_blockedMiddleGaugeFormula` is
  now tagged with `TNLean.PEPS.hasFactorizedLocalGauge_of_localGaugeFormula`,
  which had no blueprint node and has the node's statement.
* Items 5, 7 and 8: the replacement already owns another node
  (`lem:gauge_unique_up_to_scalar`,
  `thm:peps_edgeBlockedEndpointTensorMaps_injective`,
  `thm:mpdo_block_two_as_positive_blocking`), so retagging would create a
  duplicate tag. The relinquishing nodes `thm:gauge_unique_up_to_scalar_sameMPV`,
  `thm:peps_edgeBlockedEndpointTensorMaps_injective_all` and
  `thm:mpug_czx_tensor_general_blocking` were deleted with their proofs; no
  `\uses` or `\ref` named any of them. For item 5 this also removes a node whose
  statement carried an equal-MPV hypothesis that the Lean statement only kept
  to match it.

## Documentation

`docs/glossary.md` names `primitivePaper_iff_hasEventuallyFullKrausRank` as
the Kraus-span form of Wolf Theorem 6.8.
`docs/paper-gaps/peps_injective_ft_section3_route.tex` cites the per-edge
endpoint injectivity theorem only, and
`docs/paper-gaps/mpu_czx_tensor_normalization.tex` cites
`MPOTensor.blockTwo_eq_blockTensor_reindex` for the blocking step.
