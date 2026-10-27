# Left-block monotonicity

The theorem `TNLean.MPS.AreaLaw.leftBlock_mono` now belongs to
`TNLean/MPS/AreaLaw/OpenMPS.lean`, immediately after the membership criterion
for left blocks. Its name, statement and proof are unchanged. Both sequential
truncation and the three-way cut coordinates use this elementary fact without
an additional import.

The removed theorem `TNLean.MPS.AreaLaw.leftBlock_sub_one_subset` was its
specialization to the inclusion of the first `k - 1` sites in the first `k`
sites. Every non-Archive use now applies `leftBlock_mono (Nat.sub_le k 1)`
directly. No compatibility alias remains. The cut-coordinate blueprint entry
no longer lists the removed theorem; the existing general monotonicity theorem
retains its declaration annotation in the sequential-truncation entry.

Only the proofs of these subset inclusions change in the cut coordinates and
trimmed-witness statements. Their hypotheses and conclusions are unchanged.
