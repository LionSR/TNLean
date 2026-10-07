# Removal of the root-namespace tangent-line logarithm bound

`TNLean/MPS/Preparation/DepthLowerBoundConstant.lean` declared the tangent-line
bound `log x ≤ l x - 1 - log l` (for `x, l > 0`) as the root-namespace theorem
`Real.log_le_mul_sub_one_sub_log`. It had one use, in the proof of
`MPSTensor.exists_mul_log_le_of_infidelity_le_one_half_of_isNormal` in the same
file, and one citation, in the `\lean{...}` list of the blueprint entry
`thm:ldp_depth_lower_bound_constant`.

## Removed declaration and its replacement

| Removed declaration | Replacement |
|---|---|
| `Real.log_le_mul_sub_one_sub_log` | the three-line local derivation from Mathlib's `Real.log_le_sub_one_of_pos` and `Real.log_mul` at its single call site |

The blueprint tag is dropped from `thm:ldp_depth_lower_bound_constant`. The two
statements of that entry keep their tags. No other use exists in `TNLean`,
`blueprint`, `docs` or `scripts`.
