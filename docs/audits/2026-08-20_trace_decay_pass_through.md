# Rectangular trace-decay pass-through deletion audit

This cleanup uses the repository-local exact-pass-through exception in
`docs/MATHLIB_style.md` §Deprecation.

| Removed declaration | Direct replacement |
|---|---|
| `MPSTensor.tendsto_trace_pow_of_tendsto_zero_rect` | `ContinuousLinearMap.tendsto_trace_pow_of_tendsto_zero` |

The removed public theorem was an exact pass-through wrapper with no independent
mathematical content. Its sole non-Archive Lean use now calls the replacement
directly. A repository-wide exact-name search found no remaining non-Archive use
or blueprint `\lean{...}` tag for the removed declaration.
