# Route-neutral inputs for the grouped vertical decomposition (issue #6855 section 4)

The grouped-sector part of the vertical canonical form of a matrix product density
operator existed twice: once under normalized BNT-refined horizontal form and once
under literal CPSV canonical form. The two families of theorems had identical
twelve-hypothesis signatures and identical proof bodies; they differed only in the
entry hypothesis and in the name of the theorem that compares the Gram dressings of
two positive vertical corners of a common representative. The comparison itself was
already available as a canonical-form-independent property,
`MPOTensor.HasGroupedCornerGramDressing`, and the generic Gram-conjugation and
Gram-scalar theorems over it were already in
`TNLean/MPS/MPDO/GroupedSectorGram.lean`. This change states the remaining two steps
of that chain once, over the same property, and removes the duplicated families.

The separation of the two canonical-form predicates is preserved. No implication
between `MPOTensor.IsHorizontalCF` and `MPSTensor.IsCPSVCanonicalForm` is proved or
used. Each predicate supplies the route-neutral inputs on its own, from its own
grouping theorem and its own pairwise Figure 8 theorem, exactly as the previously
accepted capstone `MPOTensor.verticalCF_of_grouping_and_gramDressing` already did.

## What was added

`TNLean/MPS/MPDO/VerticalBNTGrouping.lean` names the pair of inputs that the grouped
vertical construction consumes.

| Declaration | Content |
|---|---|
| `MPOTensor.HasVerticalBNTGroupingInputs` | the phase-class grouping with physical isometries and the grouped-corner Gram dressing |
| `MPOTensor.HasVerticalBNTGroupingInputs.verticalCF` | those two inputs give vertical canonical form |
| `MPOTensor.IsHorizontalCF.hasGroupedCornerGramDressing` | the horizontal Gram dressing |
| `MPOTensor.IsHorizontalCF.hasVerticalBNTGroupingInputs` | both inputs from horizontal form |
| `MPSTensor.IsCPSVCanonicalForm.hasGroupedCornerGramDressing` | the literal Gram dressing |
| `MPSTensor.IsCPSVCanonicalForm.hasVerticalBNTGroupingInputs` | both inputs from literal form |

Two route-neutral theorems replace the four deleted ones:

| Declaration | Host |
|---|---|
| `MPOTensor.grouped_sector_exists_unitary_normalization_of_dressing` | `TNLean/MPS/MPDO/GroupedGramNormalization.lean` |
| `MPOTensor.exists_normalized_grouped_sector_maps_of_dressing` | `TNLean/MPS/MPDO/NormalizedGroupedSectors.lean` |

## What was removed and what replaces it

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.IsMPDO.grouped_sector_gram_conj_eq` | `MPOTensor.grouped_sector_gram_conj_eq_of_dressing` |
| `MPSTensor.IsCPSVCanonicalForm.grouped_sector_gram_conj_eq` | `MPOTensor.grouped_sector_gram_conj_eq_of_dressing` |
| `MPOTensor.IsMPDO.grouped_sector_gram_eq_pos_smul_one` | `MPOTensor.grouped_sector_gram_eq_pos_smul_one_of_dressing` |
| `MPSTensor.IsCPSVCanonicalForm.grouped_sector_gram_eq_pos_smul_one` | `MPOTensor.grouped_sector_gram_eq_pos_smul_one_of_dressing` |
| `MPOTensor.IsMPDO.grouped_sector_exists_unitary_normalization` | `MPOTensor.grouped_sector_exists_unitary_normalization_of_dressing` |
| `MPSTensor.IsCPSVCanonicalForm.grouped_sector_exists_unitary_normalization` | `MPOTensor.grouped_sector_exists_unitary_normalization_of_dressing` |
| `MPOTensor.IsMPDO.exists_normalized_grouped_sector_maps` | `MPOTensor.exists_normalized_grouped_sector_maps_of_dressing` |
| `MPSTensor.IsCPSVCanonicalForm.exists_normalized_grouped_sector_maps` | `MPOTensor.exists_normalized_grouped_sector_maps_of_dressing` |

Four modules are deleted: `TNLean/MPS/MPDO/GroupedFigure8.lean`,
`TNLean/MPS/MPDO/CPSVGroupedFigureEight.lean`,
`TNLean/MPS/MPDO/CPSVGroupedGramNormalization.lean`,
`TNLean/MPS/MPDO/CPSVNormalizedGroupedSectors.lean`. No compatibility aliases are
kept: the repository does not retain dead declarations as deprecated aliases, every
non-Archive use is migrated, and no declaration tag names an old name after this
change.

## Reference audit

Both Gram-conjugation theorems and both unitary-normalization theorems had no Lean
consumer outside their own module. `grouped_sector_gram_eq_pos_smul_one` was used
only by its own module's sibling and by the normalized-maps theorem of the same
family. The normalized-maps theorems had exactly two consumers, both of which now
call the route-neutral theorem with their own Gram dressing:
`TNLean/MPS/MPDO/RFPPositiveFusionDecomposition.lean` for the horizontal route and
`TNLean/MPS/MPDO/CPSVVerticalDecomposition.lean` for the literal route. The two
capstone wrappers `MPOTensor.verticalCF_of_horizontalCF` and
`MPOTensor.verticalCF_of_cpsvCanonicalForm` keep their statements and now obtain the
inputs through their own smart constructor. Docstring references in
`TNLean/MPS/MPDO/CPSVVerticalBNT.lean` and `TNLean/MPS/MPDO/VerticalCF.lean` are
migrated, as are the path and declaration references in
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`,
`docs/paper-gaps/cpgsv17_vertical_diagonal_restriction.tex`, and the three ledger
entries in `docs/tactic_patterns.md` that recorded the earlier separation.

## Blueprint

Six intermediate nodes, three per route, are merged into their route-neutral nodes in
`blueprint/src/chapter/ch20_mpdo_canonical_forms_positivity_gram_normalization.tex`.

| Merged node | Surviving node |
|---|---|
| `thm:mpdo_grouped_sector_gram_conjugation` | `thm:grouped_sector_gram_conj_of_dressing` |
| `thm:cpsv_literal_grouped_sector_gram_conjugation` | `thm:grouped_sector_gram_conj_of_dressing` |
| `thm:mpdo_grouped_sector_unitary_normalization` | `thm:grouped_sector_gram_scalar_of_dressing` |
| `thm:cpsv_literal_grouped_sector_unitary_normalization` | `thm:grouped_sector_gram_scalar_of_dressing` |
| `thm:mpdo_normalized_grouped_sector_maps` | `thm:normalized_grouped_sector_maps_of_dressing` |
| `thm:cpsv_literal_normalized_grouped_sector_maps` | `thm:normalized_grouped_sector_maps_of_dressing` |

`thm:grouped_sector_gram_scalar_of_dressing` gains the unitary-normalization
conclusion of the two merged nodes together with the tag for the new theorem; its
hypotheses are unchanged, so the merged statement is weaker in hypotheses and
stronger in conclusion than either route node. `thm:normalized_grouped_sector_maps_of_dressing`
is new and carries the statement the two merged nodes shared, with the Gram-dressing
hypothesis in place of the two canonical forms. The three dependency references to
merged labels, one in the same chapter and two in chapter 21, now name the surviving
nodes.

The scope-restriction marker on `thm:mpdo_grouped_sector_unitary_normalization`
recorded that the horizontal hypothesis is stronger than the literal CPSV hypothesis.
That restriction no longer applies at the merged node, whose hypothesis is the
Gram-dressing property that both canonical forms supply. The scope-restriction
markers on the nodes that remain specific to horizontal form, including the capstone
node and the chapter 21 product-law node, are untouched, and the literal anchors
`thm:vertical_cf_of_cpsv_canonical_form`,
`thm:mpdo_literal_cpsv_rfp_to_bnt_fusion_tensor`, and
`thm:mpdo_literal_cpsv_vertical_decomposition` keep their statements and tags.

## Retained and deferred

`TNLean/MPS/MPDO/CPSVVerticalBNT.lean` and `TNLean/MPS/MPDO/CPSVFigureEight.lean`
are the genuinely route-specific literal content and are retained; they are the two
theorems the literal smart constructor calls. The remaining twin families named in
issue #6855 section 4, the vertical-decomposition, product spectral-family,
product corner-positivity, product fusion-decomposition, and
basis-of-normal-tensors fusion-tensor pairs, are unchanged here. Those pairs fork on
three further route-neutral clauses, invariant projector closure, absence of periodic
vectors, and sector-compression separation, stated for the two-site block rather than
for the tensor itself. `HasVerticalBNTGroupingInputs` is the place for those fields;
they are not added in advance of the theorems that consume them.
