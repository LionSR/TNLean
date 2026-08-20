# Transfer-operator gap pass-through deletion audit

This cleanup uses the repository-local exact pass-through exception in
`docs/MATHLIB_style.md`.

## Removed declarations and replacements

| Removed declaration | Direct replacement |
|---|---|
| `MPSTensor.geometric_bound_of_spectralRadius_lt_one` | `_root_.geometric_bound_of_spectralRadius_lt_one` |
| `MPSTensor.pow_tendsto_zero_of_spectralRadius_lt_one` | `_root_.pow_tendsto_zero_of_spectralRadius_lt_one` |
| `MPSTensor.IsIdempotentElem.eq_zero_of_spectralRadius_lt_one` | `_root_.IsIdempotentElem.eq_zero_of_spectralRadius_lt_one` |

Each removed declaration was an exact deprecated alias of the listed theorem. None added a
hypothesis, changed a conclusion, or contained an independent argument. The compatibility module
`TNLean.Spectral.TransferOperatorGapCommon` contained no other declaration.

All non-Archive TNLean imports of the compatibility module have been replaced by direct imports of
`TNLean.Analysis.SpectralRadiusPowerDecay`. A repository-wide exact-name search found no remaining
non-Archive use of the aliases, and no blueprint `\lean{...}` tag cites any of them.
