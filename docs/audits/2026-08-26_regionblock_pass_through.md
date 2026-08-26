# RegionBlock pass-through retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. Each declaration below forwarded to an
existing theorem, projected a bundled-structure field, or named a proof step
now written at the use site. At the audited head each had no non-`Archive`
consumer and no Blueprint `\lean{...}` tag, so no transition declaration was
left behind.

| Removed | Replacement |
|---|---|
| `TNLean.PEPS.exists_regionEdgeGauge_of_blockCoeffTransfer` | `TNLean.PEPS.exists_regionEdgeGauge_of_coeffTransfer` (`TNLean/PEPS/RegionBlock/RegionReconcile.lean`; statement byte-identical) |
| `TNLean.PEPS.regionInsertedCoeff_eq_of_realizes` | `TNLean.PEPS.regionInsertedCoeff_transfer_of_realizes` (`TNLean/PEPS/RegionBlock/Recovery2.lean`) |
| `TNLean.PEPS.agreeOffEdge_overrideEdge` | `fun _ hf => (overrideEdge_ne … hf).symm` from the `@[simp]` lemma `TNLean.PEPS.overrideEdge_ne` (`TNLean/PEPS/RegionBlock/CoarseThreeSite7.lean`) |
| `TNLean.PEPS.overrideEdge_coarse_rc` | `TNLean.PEPS.overrideEdge_ne` at `coarseEdgeRC` (`decide` discharges the side condition) |
| `TNLean.PEPS.overrideEdge_coarse_bc` | `TNLean.PEPS.overrideEdge_ne` at `coarseEdgeBC` (`decide` discharges the side condition) |
| `TNLean.PEPS.CrossTripleAgreesAwayRB.of_tripleAgrees` | the anonymous constructor `⟨h.2.1, h.2.2⟩` at the use site |
| `TNLean.PEPS.regionBlockedTensorInjective_union_of_isVertexInjective` | `(regionInjectivityUnionClosure_of_isVertexInjective A hA hpos).union_injective` (`TNLean/PEPS/RegionBlock/UnionClosure.lean`), which carries the source implication shape `inj(R) → inj(S) → inj(R ∪ S)`; the `@[simp]` `rfl` lemma `regionInjectivityDataOf_isInjective` bridges `RegionInjectivityData.IsInjective` and `RegionBlockedTensorInjective` |

## Notes on individual rows

The first row moves the cited name, not the content. The footnote at
`docs/paper-gaps/peps_normal_ft_section3_route.tex` heads its list
"Formal declarations (block frame, sorry-free)"; the surviving declaration has
the same statement and lives in a sorry-free module, so the footnote's claim is
unchanged. The only difference is that the surviving name lives in
`TNLean/PEPS/RegionBlock/RegionReconcile.lean` rather than in the block-frame
module, and the footnote was redirected in the same change.

The last row is the one that needed an argument. The removed theorem's
docstring recorded a deliberate rationale: its two region hypotheses were kept
unused so that the statement matched the source implication of
arXiv:1804.04964, Section 3, Lemma `lem:injective_union`. The removal is
justified only because that source-shaped implication survives verbatim, as the
`union_injective` field of the union-closure instance immediately above it. The
replacement is therefore *not* `regionBlockedTensorInjective_of_isVertexInjective`,
which proves the unconditional statement and would silently drop the source
shape.

No import was removed. In particular
`TNLean/PEPS/RegionBlock/BlockCoeffTransfer.lean` keeps its import of
`TNLean.PEPS.RegionBlock.RegionReconcile`: `transferCoeff`, still used in that
file, is reachable only along that import path.
