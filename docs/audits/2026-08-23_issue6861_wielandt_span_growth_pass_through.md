# Issue #6861: Wielandt span-growth pass-through retirement

This cleanup uses the exact pass-through exception in
`docs/project_conventions.md`. The following `MPSTensor` declarations had the
same statements as existing finite-family theorems and contributed no separate
mathematical argument:

| Removed declaration | Canonical replacement |
|---|---|
| `MPSTensor.cumulativeSpan_mono'` | `Kraus.cumulativeSpan_mono'` |
| `MPSTensor.one_mem_cumulativeSpan` | `Kraus.one_mem_cumulativeSpan` |
| `MPSTensor.wordSpan_eq_top_of_ge_of_isUnit` | `Kraus.wordSpan_eq_top_of_ge_of_isUnit` |

All non-Archive consumers now use the corresponding `Kraus` declarations
directly. No blueprint `\lean{...}` tag cited any of the removed names. The
remaining declarations in the two span-growth modules are retained because
they express tensor-network notions such as Kraus rank and injectivity index,
or because QICLean provides no theorem with the same statement.
