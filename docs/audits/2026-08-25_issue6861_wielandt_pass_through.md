# Issue #6861: Wielandt pass-through audit at current main

Audited at TNLean `0f80092e302558e7be7076bcd2c321b6b180eef0`, with QICLean v0.2.1 at
`df9ded03a81d2c02ce1962331777a7a1a87c57b4`.

The project pass-through exception applies: each declaration is a literal
forward, every non-Archive consumer is migrated, and no Blueprint tag names it.

| Removed declaration | Single source of truth | Migrated consumer |
|---|---|---|
| `MPSTensor.cumulativeSpan_mono'` | `Kraus.cumulativeSpan_mono'` | `BurnsideMatrix` |
| `MPSTensor.one_mem_cumulativeSpan` | `Kraus.one_mem_cumulativeSpan` | `BurnsideMatrix` |
| `MPSTensor.wordSpan_eq_top_of_ge_of_isUnit` | `Kraus.wordSpan_eq_top_of_ge_of_isUnit` | `Bounds` |

At the audited head, repository-wide search found only the declarations and five
`BurnsideMatrix` call sites plus one `Bounds` call site; no Archive or docs use.
The two defining modules remain because their other results are MPS-specific;
only these duplicate statements are retired in favor of the QICLean owners.
