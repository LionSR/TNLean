# The anomalous `ℤ/3` defect square as a direct sum of pair data

This audit records the removal of the explicit 25-coordinate gauge and flag data of the
compression of the stacked square of the anomalous `ℤ/3` condensation defect. It is the audit
note required by `docs/project_conventions.md` §Style. All non-`Archive` uses are migrated, no
blueprint `\lean{...}` tag cites a removed name, and no compatibility alias is kept.

## Removed declarations

In `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousDefectCompression.lean`:

- `Z3Anomalous.pairGaugeEis`, `Z3Anomalous.pairGaugeInvEis`, `Z3Anomalous.pairGauge_mul_inv`,
  `Z3Anomalous.pairGaugeInv_mul`: the nine pair gauges over `ℤ[ω]`.
- `Z3Anomalous.squareGaugeEis`, `Z3Anomalous.squareGaugeInvEis`,
  `Z3Anomalous.squareGauge_mul_inv`, `Z3Anomalous.squareGaugeInv_mul`: their direct sum on the
  25 bond coordinates.
- `Z3Anomalous.pairConjEis`, `Z3Anomalous.pairConjTable`, `Z3Anomalous.pairConjEis_eq`,
  `Z3Anomalous.square_conj`: the conjugated letters of the square.
- `Z3Anomalous.pairOrdTable`, `Z3Anomalous.squareOrd`, `Z3Anomalous.targetOffset`,
  `Z3Anomalous.targetOffset_add_lt`, `Z3Anomalous.zeroSlotSigma`, `Z3Anomalous.blockSigma`,
  `Z3Anomalous.blockOfBond`, `Z3Anomalous.squareCoord`: the flag order and the labelling of the
  bond coordinates by the graded block space.
- The private clauses `square_triangular`, `square_matched`, `square_unmatched`.

## Replacement

`Z3Anomalous.defectSquare_compression` is now
`MPSTensor.MultiBlockCompression.directSum pairCompression squareBond
defectSquare_eq_blockDiagonal`, the direct sum of the nine pair-block data
(`Z3Anomalous.pairCompression`) along the block-diagonal form of the square
(`Z3Anomalous.defectSquare_eq_blockDiagonal`). The general construction
(`TNLean/MPS/FundamentalTheorem/Reduction/MultiBlockDirectSum.lean`) supplies the gauge, the
block order and the coordinate labelling once for every example, together with the identity of
the assembled remainder as the direct sum of the block remainders, which gives the sharp
nilpotency order three (`Z3Anomalous.defectSquare_evalWord_remainder_eq_zero`,
`Z3Anomalous.defectSquare_remainder_mul_ne_zero`). The flag order of the assembled datum is the
block-by-block order rather than the interleaved order of the data file; the statements about
the datum (targets, reductions, biorthogonality, the dimension count) are unchanged.
