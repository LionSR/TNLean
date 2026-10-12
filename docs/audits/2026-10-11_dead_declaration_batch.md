# Dead declarations removed in one batch (2026-10-11)

This batch removes declarations with no consumers that the proof-debt surveys
had already identified (#4564, #7911, #7913, #7915, #7917). Before each
deletion, every final name component was searched across `TNLean`,
`TNLeanTest`, `blueprint/src`, `docs` and `scripts` on `main` at `128718a7`.
None of the removed declarations had a Lean consumer, and none carried a
`sorry` or an `axiom`. Every Blueprint `\lean{...}` tag and paper-gap
`\leanid{...}` that cited a removed name is edited in the same change.

## Removed declarations and their replacements

| Removed declaration | Issue | Replacement |
|---|---|---|
| `MPOTensor.productBondSwapEquiv_self` (`MPS/MPDO/PhysicalAdjoint.lean`) | #4564 | none needed: no consumer |
| `MPOTensor.embedLocalOperator_mem_unitaryGroup` (`MPS/MPDO/PhysicalGibbsEmbedding.lean`) | #4564 | none needed: no consumer; it follows from `embedLocalOperator_conjTranspose`, `embedLocalOperator_mul` and the unit law, which stay |
| `MPOTensor.TwistedDimer.tau_one_sum` (`MPS/MPDO/TwistedDimer.lean`) | #4564 | none needed: no consumer; `simp [tau]` proves it |
| `Matrix.isStarProjection_swapAntisymmetricProjection` (`MPS/MPU/Examples/SwapPath.lean`) | #4564 | none needed: no consumer; it is `(isStarProjection_swapSymmetricProjection d).one_sub` |
| `MPSTensor.AppendixBStructuralData.appendixBQAX_factor_action` (module `MPS/RFP/AppendixBFactorAction.lean`, deleted) | #7911 | `MPSTensor.leftPairLift_toMatrix_reindex`, of which it was the instance at `appendixBQAXOnCoeffSpace` |
| `MPSTensor.AppendixBStructuralData.appendixBQXB_factor_action` (same module) | #7911 | `MPSTensor.rightPairLift_toMatrix_reindex`, of which it was the instance at `appendixBQXBOnCoeffSpace` |
| `MPSTensor.fundamentalTheorem_periodic_proportional_of_isPeriodic` (`MPS/Periodic/FundamentalTheorem.lean`) | #7915 | `MPSTensor.fundamentalTheorem_periodic_proportional` applied to `PeriodicOverlapHypothesis.ofIsPeriodic`, which was its whole body |
| `MPOTensor.IsMPUSimple.sourceV_transpose_isIsometry` (`MPS/MPU/SourceVCompleteNetwork.lean`) | #7917 | `MPOTensor.IsMPUCanonicalFormII.sourceV_isIsometry` for the source gate; the transposed-weight auxiliary statement was the residue of a route that D13 excludes |
| private `MPSTensor.ft_sector_bnt_equal_mps_unitaryGauge_literal` (`MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean`) | #7913 | renamed to the public `MPSTensor.fundamentalTheorem_equal_canonicalForm_unitary`, whose former body was a bare call to it; the statement is unchanged |

## Prose repointed

- `ch13_parent_hamiltonian_commuting_gap_appendix_b_commutation.tex`: the two
  factor-action theorems keep their statements, `\leanok` marks and
  `\uses{thm:pair_lift_kronecker_matrices, ...}`; their printed proofs already
  apply that theorem, so they lose only the forwarder tags.
- `docs/paper-gaps/cpsv16_parent_commuting_hamiltonian_scope.tex`: the
  footnote cites only the two generic pair-lift identities and the sentence
  says that the Appendix B equations are their instances.
- `docs/paper-gaps/dccsp17_periodic_overlap_route_alignment.tex` and the
  module docstring of `MPS/Periodic/FundamentalTheorem.lean` name the one
  remaining block-matching theorem and `PeriodicOverlapHypothesis.ofIsPeriodic`.
- `docs/paper-gaps/mpu_source_cut_orientation.tex` drops the sentence that
  recorded the transposed-weight theorem as retained.
