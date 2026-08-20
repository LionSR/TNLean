# Issue #6706: full rank-one extraction pass-through deletion audit

This cleanup uses the repository-local exact pass-through exception in
`docs/MATHLIB_style.md` §Deprecation. The removed declaration had no independent
mathematical content:

- `MPSTensor.pow_single_mem_wordSpan` forwarded exactly to
  `Kraus.pow_single_mem_wordSpan`.

A repository-wide search found no active TNLean or Archive caller of the old
name, and no blueprint `\lean{...}` tag cites it. The exact alias therefore
qualifies for immediate removal under that exception rather than a deprecation
period. `Kraus.pow_single_mem_wordSpan` remains the canonical theorem and sole
proof owner.
