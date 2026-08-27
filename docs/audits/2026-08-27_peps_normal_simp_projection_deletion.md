# Normal-tensor PEPS slice: fifteen zero-reference simp projection lemmas

Fifteen `@[simp]` lemmas across four modules of the normal-tensor PEPS
development had no reference anywhere in the repository, in the blueprint, or in
the documentation. Each states a projection or an unfolding that already holds by
`rfl`, so none of them was doing work that a surviving proof needs; the root
build is clean without them. They are deleted outright rather than
de-attributed, so no orphan statement is left behind.

The pass-through exception of `docs/project_conventions.md` §Style applies: none
of the fifteen names is cited by a blueprint `\lean{...}` tag, and the table
below names each removed declaration with its replacement.

## Removed declarations

| Removed | Replacement |
|---|---|
| `TNLean.PEPS.NormalSquareLatticeRectangleInjectivityHypotheses.toRectangular_twoByThreeRegion` (`TNLean/PEPS/NormalBlocking.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.NormalSquareLatticeRectangleInjectivityHypotheses.toRectangular_threeByTwoRegion` (`TNLean/PEPS/NormalBlocking.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.scaleVertex_bondDim` (`TNLean/PEPS/NormalBondDimension.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.normalSquareHorizontalTranslatedEdge_blockingDatum_interior_blue` (`TNLean/PEPS/NormalEdgeBlockingInterior.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.normalSquareHorizontalTranslatedEdge_blockingDatum_interior_complement` (`TNLean/PEPS/NormalEdgeBlockingInterior.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.normalSquareVerticalTranslatedEdge_blockingDatum_interior_red` (`TNLean/PEPS/NormalEdgeBlockingInterior.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.normalSquareVerticalTranslatedEdge_blockingDatum_interior_blue` (`TNLean/PEPS/NormalEdgeBlockingInterior.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.normalSquareVerticalTranslatedEdge_blockingDatum_interior_complement` (`TNLean/PEPS/NormalEdgeBlockingInterior.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.regionInjectivityDataPair_isInjective` (`TNLean/PEPS/NormalPairBlocking.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.NormalEdgeBlockingData.pairLeft_red` (`TNLean/PEPS/NormalPairBlocking.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.NormalEdgeBlockingData.pairLeft_blue` (`TNLean/PEPS/NormalPairBlocking.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.NormalEdgeBlockingData.pairLeft_complement` (`TNLean/PEPS/NormalPairBlocking.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.NormalEdgeBlockingData.pairRight_red` (`TNLean/PEPS/NormalPairBlocking.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.NormalEdgeBlockingData.pairRight_blue` (`TNLean/PEPS/NormalPairBlocking.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |
| `TNLean.PEPS.NormalEdgeBlockingData.pairRight_complement` (`TNLean/PEPS/NormalPairBlocking.lean`) | none needed; the surviving consumers prove the projection by `rfl` at the use site |

## Withdrawn from the slice

`TNLean.PEPS.normalSquareHorizontalTranslatedEdge_blockingDatum_interior_red` is
kept. It is cited through `\leanid{}` at
`docs/paper-gaps/peps_normal_ft_section3_route.tex:1392`, so deleting it would
break a named reference in the paper-gap record for the route through Section 3
of arXiv:1804.04964. Its section header in
`TNLean/PEPS/NormalEdgeBlockingInterior.lean` is reworded from the plural to the
singular, since it is now the only projection lemma in that section: the header
describes the red region of the horizontal translated interior blocking datum
alone.

## What survives

The definitions the deleted lemmas projected are all load-bearing and untouched:
`toRectangular`, `scaleVertex`, `normalSquareHorizontalTranslatedEdge_blockingDatum_interior`,
`normalSquareVerticalTranslatedEdge_blockingDatum_interior`,
`regionInjectivityDataPair`, `NormalEdgeBlockingData.ofLE`,
`NormalEdgeBlockingData.pairLeft` and `NormalEdgeBlockingData.pairRight`. The
two pair projections in particular are used by the absorbed-family, bond-dimension
and general-fundamental-theorem modules of the normal-tensor development.

## Verification

Root `lake build` completes successfully with the package lean options on the
first attempt, which exercises every importer of the four edited modules; no
surviving proof was relying on any of the fifteen lemmas through a bare `simp`.
`check_forbidden_lean_tokens.py`, `check_reader_facing_prose.py`,
`check_numbered_lean_files.py`, `check_oversized_lean_files.py` and
`generate_import_aggregators.py --check` are clean. The slice removes 109 lines
net and burns down part of ledger entry S2 in `docs/proof_debt_ledger.md`.
