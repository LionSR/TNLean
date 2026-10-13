# Overlap-crossing union boundary: the primed alias (2026-10-13)

`TNLean/PEPS/RegionBlock/UnionInjectivityOverlap3.lean` carried
`TNLean.PEPS.not_isRegionBoundaryEdge_union_of_overlapCrossing'`, a verbatim
restatement of `TNLean.PEPS.not_isRegionBoundaryEdge_union_of_overlapCrossing`
(`TNLean/PEPS/RegionBlock/UnionInjectivityOverlapSetup.lean`, which the file
imports): an edge with one endpoint in `R₁ ∩ R₂` and the other in `R₁ \ R₂` is
not a boundary edge of `R₁ ∪ R₂`. Its proof was the unprimed lemma, and its only
consumer was `regionBoundaryLabel_union_interCrossGlue` in the same file. No
blueprint `\lean{...}` tag and no test cited it.

## Removed declarations and their replacements

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.not_isRegionBoundaryEdge_union_of_overlapCrossing'` | `TNLean.PEPS.not_isRegionBoundaryEdge_union_of_overlapCrossing` |
