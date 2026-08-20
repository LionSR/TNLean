# Trace-expansion pass-through deletion audit

This cleanup uses the repository-local exact pass-through exception in
`docs/MATHLIB_style.md` §Deprecation.

## Removed declarations and replacements

| Removed declaration | Direct replacement |
|---|---|
| `MPSTensor.linearMap_trace_eq_sum_apply_single` | `Matrix.linearMap_trace_eq_sum_apply_single` |
| `MPSTensor.entry_mul_single_mul` | `Matrix.entry_mul_single_mul` |

Both removed lemmas were exact forwards to the listed matrix lemmas and had the
same conclusions. The compatibility statements carried unused `[NeZero D₁]`
and `[NeZero D₂]` instances that the more general matrix lemmas do not require.
They had no independent mathematical content.
All non-Archive TNLean uses now call the matrix lemmas directly. The sole
blueprint declaration tag on an old name now cites
`Matrix.linearMap_trace_eq_sum_apply_single`, and no blueprint tag cites
`MPSTensor.entry_mul_single_mul`. A repository-wide exact-name search found no
remaining non-Archive use or blueprint tag for either removed declaration.
Their compatibility module, `TNLean.Spectral.TraceExpansion`, therefore
qualifies for immediate removal under the repository-local exception rather
than a deprecation period.
