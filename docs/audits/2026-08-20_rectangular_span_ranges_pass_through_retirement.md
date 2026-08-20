# Rectangular-span range pass-through retirement

## Scope

`TNLean/Wielandt/RectangularSpan/Ranges.lean` contained six declarations in the
`MPSTensor` namespace that forwarded exactly to existing matrix declarations:

| Removed declaration | Canonical replacement |
|---|---|
| `MPSTensor.col_mul` | `Matrix.col_mul` |
| `MPSTensor.mem_range_mulLeft_iff_cols` | `Matrix.mem_range_mulLeft_iff_cols` |
| `MPSTensor.colRangeSubmodule` | `Matrix.colRangeSubmodule` |
| `MPSTensor.colRangeSubmoduleEquiv` | `Matrix.colRangeSubmoduleEquiv` |
| `MPSTensor.range_mulLeft_eq_pi` | `Matrix.range_mulLeft_eq_pi` |
| `MPSTensor.finrank_range_mulLeft` | `Matrix.finrank_range_mulLeft` |

Each removed declaration had no independent statement or proof content beyond
its canonical replacement in `TNLean/Algebra/MatrixMulRange.lean`.

## Reference audit

After the rectangular-span universality relocation, one internal theorem still
used `MPSTensor.finrank_range_mulLeft` through an unqualified name. This use in
`TNLean.Wielandt.RectangularSpan.Universality` now invokes
`Matrix.finrank_range_mulLeft` directly and imports its owner module. No other
non-Archive use of a removed `MPSTensor` name remained, and no blueprint
`\lean{...}` tag cited one. The deleted module had two remaining importers:
`TNLean.Wielandt.RectangularSpan.Basic`, where the import was unused, and the
generated `TNLean.Wielandt.RectangularSpan` aggregator.

This removal invokes the repository-local exact-pass-through exception in
`docs/MATHLIB_style.md`: every old declaration forwards exactly to the mapped
matrix declaration above, all internal uses have been migrated or were absent,
no blueprint tag refers to an old name, and the pull request records the same
replacement map.
