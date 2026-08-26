# Vertical-sector hypothesis forwarding-abbreviation retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. The four declarations below were
`abbrev`s over the parent structure's own projections: each took a
`VerticalSectorHypotheses` argument and unfolded to the corresponding field of
its `VerticalSectorFixedGeneratorHypotheses` parent.

| Removed | Replacement |
|---|---|
| `MPOTensor.VerticalSectorHypotheses.Tbar` | `MPOTensor.VerticalSectorFixedGeneratorHypotheses.Tbar` |
| `MPOTensor.VerticalSectorHypotheses.Sbar` | `MPOTensor.VerticalSectorFixedGeneratorHypotheses.Sbar` |
| `MPOTensor.VerticalSectorHypotheses.SbarTbar` | `MPOTensor.VerticalSectorFixedGeneratorHypotheses.SbarTbar` |
| `MPOTensor.VerticalSectorHypotheses.TbarSbar` | `MPOTensor.VerticalSectorFixedGeneratorHypotheses.TbarSbar` |

All four lived in `TNLean/MPS/MPDO/VerticalSectorGeneration.lean`; all four
replacements are the parent structure's own definitions.

## What was checked

No call site needed migration. Every use is unqualified dot notation — `h.Tbar`,
`h.Sbar`, `h.SbarTbar`, `h.TbarSbar` on a `VerticalSectorHypotheses` term — and
`structure VerticalSectorHypotheses … extends
VerticalSectorFixedGeneratorHypotheses` makes dot notation resolve through the
parent projection once the shadowing abbreviations are gone. The uses are
spread over `VerticalSectorTracePreservation.lean`,
`VerticalSectorIdentity.lean`, `VerticalSectorRelabeling.lean`, and
`VerticalSectorCompletePositivity.lean`; a repository-wide search for the
qualified spellings `VerticalSectorHypotheses.Tbar` and its three siblings
returned no hit outside the removed block itself.

Rewriting the uses to `h.toVerticalSectorFixedGeneratorHypotheses.Tbar` was
considered and rejected: it would lengthen 44 call sites for no gain, since the
`extends` projection already supplies exactly that term.

## Blueprint

No blueprint `\lean{...}` tag names any of the four. The three tagged theorems
in the affected files —
`MPOTensor.transportedVerticalSector_composites_tracePreserving`,
`…_traceAdjointSchwarz`, and `…_eq_id` — are untouched, so no redirect is
needed and no transition declaration is warranted.
