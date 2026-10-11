# Diagonal Z2 x Z2 anomaly declarations replaced by the full-group computation

This audit records the declarations removed from
`TNLean/MPS/Examples/AnomalousCondensation/Z2Z2AnomalyClass.lean` when the
anomaly computation for the diagonal subgroup `{e, xy}` was replaced by the
computation for the full group, carried out for the dressed exact
representation `Z2Z2Condensation.kleinFamily`. It is the audit note required by
`docs/project_conventions.md` §Style. No blueprint `\lean{...}` tag cites a
removed name, and no compatibility alias is kept. The diagonal statement is now
the `xy` case of the full-group result.

All names are in the namespace `Z2Z2Condensation`.

## Removed declarations and their replacements

- `diagFamily`, `diagFamily_isNormalRepresentation`: `pairFamily kxyTensor`,
  which equals `kleinFamily.comap xyHom` by `comap_xyHom`, and
  `pairFamily_kxy_isNormalRepresentation`.
- `diagFusionData`: `xyFusionData`.
- `diagFusionData_isAssociator_gen_gen_gen`, `diagFusionData_omega_gen_gen_gen`:
  `xyFusionData_isAssociator_gen_gen_gen`.
- `diagFusionData_omega_gen_one_gen`: `pairFusionData_omega_gen_one_gen`.
- `cyclicInvariant_diagFusionData`, `cyclicInvariant_omega_diag`:
  `cyclicInvariant_omega_kleinFamily_xy`.
- `not_isTrivialGaugeClass_omega_diag`:
  `not_isTrivialGaugeClass_omega_kleinFamily`.
- `diagBondDim`, `diagLabelTensor`, `diagLabelV`, `diagLabelW`: `pairBondDim`,
  `pairLabelTensor`, `pairLabelV`, `pairLabelW`.
- `diagGen`, `diagGen_pow_two`: `z2Gen`, `z2Gen_pow_two`.
- `diagCubeInt`, `diagCube`, `tripleTensor_gen_toMPSTensor`, `diagLeftTreeInt`,
  `diagRightTreeInt`, `diagFusionData_leftV_gen_gen_gen`,
  `diagFusionData_rightV_gen_gen_gen`, `diag_leftTree_evalWord`,
  `diag_leftTree_evalWord_smul`: the cube table `kxyCubeInt`, the generic trees
  `pairFusionData_leftV_gen_gen_gen` and `pairFusionData_rightV_gen_gen_gen`,
  and the integer certificate
  `MPSTensor.isDressedProportional_complexOfInt_of_mem`.

`columnInt` is kept.

## Later rename (2026-10-10)

The order-two family of `Z2Z2AnomalyClass` was generalized to
`TNLean/MPS/Symmetry/MPOSymmetry/AssociatorOrderTwo.lean`, so the replacements above now
read as follows (names outside `Z2Z2Condensation` are in `MPOTensor.GroupFamily`):

- `pairFamily A`: `orderTwoFamily eTensor A`.
- `pairFusionData`: `FusionData.orderTwo eTensor`, with the extra argument
  `mulTensor_eTensor_eTensor`.
- `pairFusionData_omega_gen_one_gen`, `pairFusionData_leftV_gen_gen_gen`,
  `pairFusionData_rightV_gen_gen_gen`, `cyclicInvariant_pairFusionData`:
  `FusionData.orderTwo_omega_gen_one_gen`, `FusionData.orderTwo_leftV_gen_gen_gen`,
  `FusionData.orderTwo_rightV_gen_gen_gen`, `FusionData.cyclicInvariant_orderTwo`.
- `pairBondDim`, `pairLabelTensor`, `pairLabelV`, `pairLabelW`: `orderTwoBondDim`,
  `orderTwoLabelTensor`, `orderTwoLabelV`, `orderTwoLabelW`.
- `z2Gen`, `z2Gen_pow_two`: `orderTwoGen`, `orderTwoGen_pow_two`.
- `pairFamily_kx_isNormalRepresentation`, `pairFamily_kxy_isNormalRepresentation`:
  `Z2Z2Condensation.orderTwoFamily_kx_isNormalRepresentation`,
  `Z2Z2Condensation.orderTwoFamily_kxy_isNormalRepresentation`.
