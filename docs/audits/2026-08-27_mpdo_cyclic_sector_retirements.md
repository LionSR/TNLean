# MPDO cyclic-sector retirements (2026-08-27)

This note records the declaration removals made in the cyclic-sector slice of
`TNLean/MPS/MPDO` on 2026-08-27, taken under the pass-through exception of
`docs/project_conventions.md` §Style. Every removal below has zero non-`Archive`
Lean consumers after migration, and every blueprint `\lean{...}` tag that named
a removed declaration was redirected in the same change. The four three-site
fiber declarations called out below are instead retained as deprecated
compatibility declarations. The retirement of the all-length non-commutation route is recorded separately in
`docs/audits/2026-08-27_mpdo_all_length_noncommutation_retirement.md`.

## Four library facts restated locally

All four were `private` in
`TNLean/MPS/MPDO/CyclicActiveFourthRegionContraction.lean` and carried no
blueprint tag.

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.PhysicalSectorFactorization.dependent_prod_fst_heq` | `congr_arg_heq`, applied to the first-projection lambda |
| `MPOTensor.PhysicalSectorFactorization.dependent_prod_snd_heq` | `congr_arg_heq`, applied to the second-projection lambda |
| `MPOTensor.PhysicalSectorFactorization.suffixContraction_last_suffix_index` | `Fin.natAdd_last` |
| `MPOTensor.PhysicalSectorFactorization.suffixContraction_castAdd_one_eq_castSucc` | definitional: `Fin.castSucc` *is* `Fin.castAdd 1`, so the one call site closes by `rfl` |

The fourth is a definitional restatement rather than a shadow of a named
library lemma. One call site rewrote by the index identity inside a `by` block
where the rewrite pattern is not syntactically present; it now discharges the
identity by `congrArg` applied to the sector word.

## Five copies of one matrix-entry congruence, collapsed to four plus a helper

The same statement — entries of a dependent family of matrices agree once the
index equation and both coordinate identifications are given heterogeneously —
was written out four times.

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.PhysicalSectorFactorization.cyclicActiveLeftBoundary_entry_eq_of_heq` | `Matrix.entry_eq_of_heq` |
| `MPOTensor.PhysicalSectorFactorization.cyclicActiveRightBoundary_entry_eq_of_heq` | `Matrix.entry_eq_of_heq` |
| `MPOTensor.PhysicalSectorFactorization.rightTensor_eq_of_heq` | `Matrix.entry_eq_of_heq` |
| `MPOTensor.PhysicalSectorFactorization.leftTensor_eq_of_heq` | `Matrix.entry_eq_of_heq` |

`Matrix.entry_eq_of_heq` is new, in
`TNLean/MPS/MPDO/PhysicalSectorFactorization.lean`. It generalizes over two
independent index families, so it covers rectangular families as well. The
matrix family enters as an explicit lambda, which is what lets the per-boundary
weight or virtual-index argument be captured rather than threaded through the
lemma signature. It is a fully generic matrix lemma parked in an MPDO module
because the companion library exports no heterogeneous-equality API and
`TNLean/Algebra/` no longer hosts generic matrix lemmas; it is an upstreaming
candidate, not a permanent home.

`MPOTensor.PhysicalSectorFactorization.neighboringOperator_entry_eq_of_heq`
stays as it was: its conclusion is indexed by a *pair* of sectors, so the
single-index-family helper does not apply.

## The dead three-site fiber split

Four declarations in `TNLean/MPS/MPDO/CyclicActiveRetainedCoordinates.lean` have
no consumer anywhere in the production corpus and no blueprint tag:
`threeSectorFiberEquiv` and its three `@[simp]` inverse-coordinate lemmas
`threeSectorFiberEquiv_symm_apply_zero`, `..._one`, and `..._two`, all in the
`MPOTensor.PhysicalSectorFactorization` namespace. They are retained as
deprecated compatibility declarations rather than deleted. New code should use
the `Fin 3` decomposition directly through `Fin.cons` and `Fin.addCases`.

`sectorCoordinateChainEquiv_apply_fst` in `CyclicActiveCutCoordinates.lean` was
*not* removed: it has plausible default-simp-set consumers in
`CyclicActiveCutStates.lean` and `CyclicActiveCutRegrouping.lean`.

## The length-one and length-two instantiations of the suffix contraction

`TNLean/MPS/MPDO/CyclicActiveSuffixMarginal.lean` contained nothing but four
instantiations of the general suffix-sector contraction at suffix lengths one
and two. The module is deleted and the generated aggregator
`TNLean/MPS/MPDO.lean` regenerated. The two public contraction abbreviations
move to the surviving `CyclicActiveFourthRegionContraction.lean` import surface
and remain available as deprecated compatibility declarations; only the two
theorem wrappers are removed.

| Audited declaration | Disposition / replacement |
|---|---|
| `MPOTensor.PhysicalSectorFactorization.oneSuffixSectorContraction` | retained with its exact former signature as deprecated compatibility for `MPOTensor.PhysicalSectorFactorization.suffixSectorContraction 1` |
| `MPOTensor.PhysicalSectorFactorization.twoSuffixSectorContraction` | retained with its exact former signature as deprecated compatibility for `MPOTensor.PhysicalSectorFactorization.suffixSectorContraction 2` |
| `MPOTensor.PhysicalSectorFactorization.reindex_reducedBlockState_add_one_eq_oneSuffixSectorContraction` | removed; use `MPOTensor.PhysicalSectorFactorization.reindex_reducedBlockState_add_eq_suffixSectorContraction L 1` |
| `MPOTensor.PhysicalSectorFactorization.reindex_reducedBlockState_add_two_eq_twoSuffixSectorContraction` | removed; use `MPOTensor.PhysicalSectorFactorization.reindex_reducedBlockState_add_eq_suffixSectorContraction L 2` |

The sole consumer,
`TNLean/MPS/MPDO/CyclicActiveAdjacentCoefficientExtraction.lean`, now imports
`CyclicActiveFourthRegionContraction` directly, and its two private helpers were
renamed `trace_suffixSectorContraction_one_eq` and
`trace_suffixSectorContraction_two_eq` so production code points directly at
the general declaration rather than the deprecated compatibility names.

In the blueprint, `def:mpdo_suffix_sector_contraction` and
`thm:mpdo_suffix_marginal_block_expansion` in
`ch21_mpdo_rfp_commuting_form_cyclic_active_markov.tex` each lose two `\lean{}`
tags and keep the general tag they already carried; both stay `\leanok`. The
prose sentence naming the cases $R=1,2,3$ is unchanged, since it names
mathematical cases rather than declarations.

This deliberately leaves one instantiation twin standing:
`threeSuffixSectorContraction` and
`reindex_reducedBlockState_add_three_eq_threeSuffixSectorContraction` are
retained, because the length-three spelling is baked into
`threeSuffixSectorContraction_eq_zero_of_not_isCyclicActiveRetainedWord` and
into the `reindex_threeSuffixSectorContraction_eq_*` pair in
`CyclicActiveFourthRegionFormula.lean`.

## Import hygiene

Twenty-four import lines were removed across ten modules of the cyclic-sector
slice; no module and no declaration leaves the tree on account of them. The
largest single case is `CyclicProjector.lean`, whose fifteen-line import block
reduces to `StackedLayers` and `HorizontalBNT`, which between them cover the
former block. Each file was pruned on its own and validated by a root build
before the next.

`CyclicActiveRetainedCoordinates.lean` keeps its import of `SourceZCLMarginal`:
it is the sole path by which `CyclicActiveFourthRegionContraction.lean` and
`CyclicActiveAdjacentCoefficientExtraction.lean` reach
`MPOTensor.reducedBlockState_add_three_eq_succ_of_isSourceZCL` and
`MPOTensor.reducedBlockState_succ_succ_eq_succ_of_isSourceZCL`.
