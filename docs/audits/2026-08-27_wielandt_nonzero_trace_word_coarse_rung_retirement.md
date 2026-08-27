# Coarse nonzero-trace-word rung retirement (2026-08-27)

`TNLean/Wielandt/Inequality/NonzeroTraceWord.lean` carried a three-rung ladder
for Lemma 1 of Sanz, Pérez-García, Wolf and Cirac, *A quantum version of
Wielandt's inequality* (arXiv:0909.5347). The coarse root rung has been
retired: under identical hypotheses it is strictly weaker than the `_sharp`
rung that sits directly beneath it.

| Removed declaration | Replacement | Migrated consumers |
| --- | --- | --- |
| `MPSTensor.exists_nonzero_trace_word_of_isPrimitivePaper` (`TNLean/Wielandt/Inequality/NonzeroTraceWord.lean`) | `MPSTensor.exists_nonzero_trace_word_of_isPrimitivePaper_sharp` (same module) | none (zero references; only the `_sharp_pos` rung is consumed, at `TNLean/Wielandt/Inequality/Bounds.lean:380`) |

## Why the sharp rung subsumes the coarse one

Both rungs take the same hypotheses: `NeZero D`, the normalization
`∑ i, (A i)ᴴ * A i = 1`, and `IsPrimitivePaper A`. The coarse rung concludes
with a word of length at most `D ^ 2`; the sharp rung concludes with a word of
length at most `D ^ 2 - krausRank A + 1`. The normalization forces at least one
nonzero matrix in the family, so `1 ≤ krausRank A` and therefore
`D ^ 2 - krausRank A + 1 ≤ D ^ 2` in natural-number arithmetic. Every
conclusion the coarse rung offers is thus already a conclusion of the sharp
rung, and the coarse bound carries no case the sharp bound misses.

## Convention

The pass-through exception at `docs/project_conventions.md` §Style applies:
every non-`Archive` use is migrated (there were none), no Blueprint
`\lean{...}` tag names the removed rung, and this note plus the pull-request
body name the removal and its replacement. No `@[deprecated] alias` is
retained. The removed name encodes no misleading terminology, so the
mathematical-language rename clause does not apply.

Both imports of the module survive: the two remaining rungs still use
`isNormal_of_isPrimitivePaper` from `TNLean.Wielandt.Primitivity.Equivalence`
and the sharp trace results from
`TNLean.Wielandt.SpanGrowth.NonzeroTraceProduct`.
