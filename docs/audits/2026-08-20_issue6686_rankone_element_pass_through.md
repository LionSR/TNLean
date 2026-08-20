# Issue #6686: rank-one element pass-through deletion audit

This cleanup uses the repository-local exact pass-through exception in
`docs/MATHLIB_style.md` §Deprecation. The removed declarations had no independent
mathematical content:

- `MPSTensor.evalWord_pow_mem_wordSpan` forwarded to
  `Kraus.evalWord_pow_mem_wordSpan`.
- `MPSTensor.exists_nonzero_pow_evalWord_mem_wordSpan_range_le` forwarded to
  `Kraus.exists_nonzero_pow_evalWord_mem_wordSpan_range_le`.

All non-Archive TNLean uses of the old names have been migrated or were absent,
and no blueprint declaration tag cites either name. Their compatibility module,
`TNLean.Wielandt.RankOne.Element`, therefore qualifies for immediate removal under
that exception rather than a deprecation period.
