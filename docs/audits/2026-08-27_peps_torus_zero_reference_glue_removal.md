# PEPS torus zero-reference window and translation glue removal

This audit records the repository-local pass-through exception
(`docs/project_conventions.md` §Style) for fifteen zero-reference declarations
removed from the torus window and translation slice.

## Why

Each entry is a projection, a `rfl` restatement, or a one-line specialization
with no non-`Archive` consumer, no `\lean{...}` tag under `blueprint/src/`, and
no prose reference anywhere in `docs/`. Six of the fifteen carried `@[simp]`
(`nestedThreeBlockGeometry_red`, `nestedThreeBlockGeometry_blue`,
`nestedThreeBlockGeometry_complement`, `restrictSubRegionσ_restrict`,
`translateEquiv_symm_apply`, `translateIncidentEdge_coe`), so a name grep could
not clear them: a `@[simp]` lemma can be load-bearing for a bare `simp` several
modules downstream without its name appearing anywhere. They were cleared by a
root `lake build`, which is green with all six gone.

## Removed declarations with replacements

Every entry has zero consumers; where a live neighbour covers the same ground it
is named.

| Removed declaration | File | Replacement |
|---|---|---|
| `nestedThreeBlockGeometry_red` | `TNLean/PEPS/TorusWindowChain2.lean` | none needed (zero consumers); the projection is `rfl` |
| `nestedThreeBlockGeometry_blue` | `TNLean/PEPS/TorusWindowChain2.lean` | none needed (zero consumers); the projection is `rfl` |
| `nestedThreeBlockGeometry_complement` | `TNLean/PEPS/TorusWindowChain2.lean` | none needed (zero consumers); the projection is `rfl` |
| `nestedThreeBlockGeometry_sdiff_red` | `TNLean/PEPS/TorusWindowChain2.lean` | none needed (zero consumers); the identity is `rfl` |
| `restrictSubRegionσ_restrict` | `TNLean/PEPS/TorusWindowChain2.lean` | none needed (zero consumers); the identity is `rfl`. The live composition lemma `restrictSubRegionσ_restrictSubRegionσ` (`TorusWindowChain4.lean`) is a different statement and stays |
| `deformedRegionStateAssembled_eq_of_curried_eq` | `TNLean/PEPS/TorusWindowChain2.lean` | none needed (zero consumers); the surviving direction `deformedRegionState_eq_of_assembled_eq` and the engine `deformedRegionStateAssembled_insert_eq_of_complementInjective` are what the chain uses |
| `bareExtendInsert_zero` | `TNLean/PEPS/TorusWindowChain5.lean` | none needed (zero consumers once `extendInsert_zero`, its only caller, went) |
| `extendInsert_zero` | `TNLean/PEPS/TorusWindowChain5.lean` | none needed (zero consumers); the additivity `extendInsert_add` and homogeneity `extendInsert_const_smul` the chain does use are kept |
| `horizontalStaircaseEndPair_subset_patch` | `TNLean/PEPS/TorusWindowChain6.lean` | none needed (zero consumers); the live inclusion is `horizontalStaircasePatch_subset_completedUnion` |
| `translateEquiv_symm_apply` | `TNLean/PEPS/TorusTranslation.lean` | none needed (zero consumers); the value is `rfl` |
| `translateIncidentEdge_coe` | `TNLean/PEPS/TorusTranslation.lean` | none needed (zero consumers); the value is `rfl`. The definition `translateIncidentEdge` is kept — it is cited by a `\lean{...}` tag in `blueprint/src/chapter/ch24_peps_ft_torus_translation_and_reference_windows.tex` |
| `bondDim_boundaryEdgeMap_translate_eq` | `TNLean/PEPS/TorusWitnessTransport.lean` | `bondDim_boundaryEdgeMap_translate`, its own proof term, which keeps live callers in `TorusGaugedWeightCovariance.lean` and `TorusCovariantAbsorbedFamily.lean` |
| `glReindex_transportedAbsorbedGauge_eq` | `TNLean/PEPS/TorusCovariantAbsorbedFamily.lean` | `glReindex_self` after substituting the two parameter equalities; `glReindex_self` stays live in the same file |
| `NormalTorusArcWindowInjectivityHypotheses.horizontalUnion_injective` | `TNLean/PEPS/TorusWindowComplement.lean` | `NormalTorusArcWindowInjectivityHypotheses.arcRectangle_injective` at the `(L+1) × K` rectangle |
| `NormalTorusArcWindowInjectivityHypotheses.verticalUnion_injective` | `TNLean/PEPS/TorusWindowComplement.lean` | `NormalTorusArcWindowInjectivityHypotheses.arcRectangle_injective` at the `L × (K+1)` rectangle |

The two `…Union_injective` lemmas are a mirror pair with identical shape and
identical (zero) reference counts; they are removed together so the tree is not
left with a half-deleted mirror. Their `namespace
NormalTorusArcWindowInjectivityHypotheses` block held nothing else and went with
them.

## Deliberately kept

`TNLean.PEPS.deformedRegionState_block` (`TNLean/PEPS/TorusDeformedWindow.lean`)
was proposed alongside these and is **not** removed. It is a source-cited
substantive identity (arXiv:1804.04964 §3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1), the correctness anchor for `deformedRegionState`, and is named in
surviving module-docstring prose. Retiring it is a dated-deprecation question,
not a pass-through one.
