# BNT fourfold fusion: retirement of the dead weighted-coordinate section

`TNLean/MPS/MPDO/BNTFourfoldFusionIndices.lean` carried two independent
families. The first declared five weighted fourfold-fusion coordinate spaces
and ten coordinate reassociations between them along the three-edge and
two-edge route patterns; the second declares the five bond-coordinate types,
their reassociation equivalences and permutation matrices, and the coherence
theorem between the two routes. The first family has had no consumer since
creation and is removed; the second is blueprint-tagged and stays.

## What was removed

Fifteen declarations, all in namespace `MPOTensor.BNTFusionIsometryFamily`,
together with their three section headers:

| Removed declaration | Kind |
|---|---|
| `FourfoldLeftAssocMultiplicity` | type abbrev |
| `FourfoldLeftInnerMultiplicity` | type abbrev |
| `FourfoldMiddleMultiplicity` | type abbrev |
| `FourfoldRightAssocMultiplicity` | type abbrev |
| `FourfoldPairMultiplicity` | type abbrev |
| `leftPathFirstSourceEquiv` | coordinate equivalence |
| `leftPathFirstTargetEquiv` | coordinate equivalence |
| `leftPathSecondSourceEquiv` | coordinate equivalence |
| `leftPathSecondTargetEquiv` | coordinate equivalence |
| `leftPathThirdSourceEquiv` | coordinate equivalence |
| `leftPathThirdTargetEquiv` | coordinate equivalence |
| `rightPathFirstSourceEquiv` | coordinate equivalence |
| `rightPathFirstTargetEquiv` | coordinate equivalence |
| `rightPathSecondSourceEquiv` | coordinate equivalence |
| `rightPathSecondTargetEquiv` | coordinate equivalence |

There is no replacement declaration and none is needed: the removed family was
never applied anywhere. The live carrier of the same index patterns is the
categorical family of `TNLean/MPS/MPDO/CompleteZipperFusionFourfold.lean`,
whose namespace `MPOTensor.CompleteZipperFusionFamily` declares its own
`Fourfold*Multiplicity` abbrevs, and whose pentagon development re-declares
the ten route equivalences as `private def` twins on that family in
`TNLean/MPS/MPDO/CompleteZipperFusionPentagon.lean`. Neither of those modules
imports `BNTFourfoldFusionIndices.lean`, so the bare-name collisions resolve
to the other carrier in every case. The index-pattern citations of
arXiv:1511.08090 (lines 279-299) carried by the removed docstrings are
reproduced on those surviving declarations, so no source citation is lost.

The module docstring lost its title and its two paragraphs describing the
weighted coordinate spaces and their edge identifications; the bond-coordinate
paragraph, the non-assertion caveat and the reference block are kept.

## What was checked

- The only importer of the module is the generated aggregator
  `TNLean/MPS/MPDO.lean`.
- Every hit for each of the fifteen names outside the file is in
  `CompleteZipperFusionFourfold.lean` or `CompleteZipperFusionPentagon.lean`
  and resolves to namespace `MPOTensor.CompleteZipperFusionFamily`; both
  modules are upstream of nothing that can see this module.
- No `\lean{}` or `\leanid{}` tag in `blueprint/src` or `docs/paper-gaps`
  names any of the fifteen declarations. The blueprint tags that mention the
  same final components cite the `CompleteZipperFusionFamily` declarations,
  and the `BNTFusionIsometryFamily` tags of
  `thm:mpdo_fourfold_bond_coordinate_coherence` name only the two surviving
  bond-coherence theorems.
- The file carries no attributes, so no simp or grind set loses a member.
- The surviving tail of the file (the bond-coordinate section) makes no
  reference to any removed name.
- The deletion precedent is commit d0f40e891, which removed the ten `*Matrix`
  companions of this same family from this same file without aliases.

## What is retained and why

The `Reassociation of four bond coordinates` section is retained in full: the
five `Fourfold*BondIndex` abbrevs, the five bond equivalences, the five bond
matrices, and the theorems `fourfoldBondReassociation_threeEdge_eq_twoEdge`
and `fourfoldBondMatrix_threeEdge_eq_twoEdge`. The two theorems carry the
`\leanok` tags of `thm:mpdo_fourfold_bond_coordinate_coherence` in
`blueprint/src/chapter/ch21_mpdo_rfp_fusion_isometries_complete_zipper_coherence.tex`,
and the section is self-contained on `Fam.bondDim`,
`mulTensorAssocEquiv`, `finProdFinEquiv` and the `PEquiv` API, so the import
of `TNLean.MPS.MPDO.BNTFinalSectorFusion` stays as it is.

## What is deferred

Nothing. The contrasting sentences of
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex` and of the complete
zipper coherence chapter that mention the positive-diagonal weighted
coordinates state a non-identification rather than a formalization and carry
no tag on the removed names, so they need no edit.
