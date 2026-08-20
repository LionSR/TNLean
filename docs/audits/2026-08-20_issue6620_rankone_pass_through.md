# Issue #6620: rank-one pass-through deletion audit

This cleanup uses the repository-local exact pass-through exception in
`docs/MATHLIB_style.md` §Deprecation. The removed declarations had no independent
mathematical content:

- `MPSTensor.exists_nonzero_trace_word_of_wordSpan_eq_top` forwarded to
  `Kraus.exists_nonzero_trace_word_of_wordSpan_eq_top`.
- `MPSTensor.exists_eigenvector_of_wordSpan_eq_top` forwarded to
  `Kraus.exists_eigenvector_of_wordSpan_eq_top`.
- `MPSTensor.biRectSpan` was definitionally equal to `Kraus.biRectSpan`.
- `MPSTensor.biRectSpan_eq_range_of_wordSpan_eq_top` forwarded to
  `Kraus.biRectSpan_eq_range_of_wordSpan_eq_top`.
- `MPSTensor.biRectSpan_le_wordSpan` forwarded to
  `Kraus.biRectSpan_le_wordSpan`.

The removed `TNLean.Wielandt.RankOne.SpanGrowth` module contained no declarations.
All non-Archive TNLean uses of the old names have been migrated or were absent,
and no blueprint declaration tag cites any old name. The three compatibility modules
therefore qualify for immediate removal under that exception rather than a deprecation
period.
