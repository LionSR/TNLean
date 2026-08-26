# Rectangular trace-decay pass-through deletion audit

This cleanup uses the repository-local exact-pass-through exception in
`docs/MATHLIB_style.md` §Deprecation.

| Removed declaration | Direct replacement |
|---|---|
| `MPSTensor.tendsto_trace_pow_of_tendsto_zero_rect` | `ContinuousLinearMap.tendsto_trace_pow_of_tendsto_zero` |
| `MPSTensor.tendsto_trace_pow_of_tendsto_zero` | `ContinuousLinearMap.tendsto_trace_pow_of_tendsto_zero` |
| `MPSTensor.linearMap_trace_pow_tendsto_one_of_spectralRadius_compl_lt_one` | `LinearMap.trace_pow_tendsto_one_of_spectralRadius_compl_lt_one` |

The removed public theorems were exact pass-through declarations with no independent
mathematical content. Their non-Archive Lean uses now call the replacements directly,
and the trace-convergence Blueprint entry cites its QICLean declaration. A
repository-wide exact-name search found no remaining non-Archive use or Blueprint
`\lean{...}` tag for the removed declarations.
