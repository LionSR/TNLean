# Weight-relative overlap normalization — candidate

Recorded for issue #10571, 2026-11-16. The shared ledger is `docs/tactic_patterns.md`.

- Seen in `MPS/Preparation/RepeatedOverlappingBlockWeights.lean` and `MPS/Preparation/RepeatedSecondOrderBlockError.lean`.
- Pattern: expand `z_j = ∑ k, β_k w_jk`, subtract `∑ j, ‖β_j‖²`, and bound the quadratic-form error divided by that positive sum by `∑ j k, ‖w_jk - δ_jk‖`.
- The estimate is uniform when the power sums nearly cancel.
- Proposed abstraction: a norm estimate for the normalized quadratic form can replace the two local `hSz` proofs if a third consumer occurs.
- The polar-state transport already uses `sum_star_copyApproxVector_mul_mpv` and `inv_mul_norm_le_norm_of_sum_norm_sq_le_one`.
- Two occurrences; no new tactic is needed. This supplementary ledger entry preserves the concurrently updated shared ledger unchanged.
