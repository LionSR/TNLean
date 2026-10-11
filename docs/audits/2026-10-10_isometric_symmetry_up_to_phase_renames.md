# Isometric-deformation symmetry stated under symmetry up to a phase

This audit records the declarations renamed when the several-block
isometric-deformation symmetry results of
`TNLean/MPS/ParentHamiltonian/BlockIsometricDeformationSymmetry.lean` were
restated under symmetry of the matrix product vectors up to a phase
(`MPSTensor.IsOnSiteSymmetricUpToPhase`) instead of exact symmetry. It is the
audit note required by `docs/project_conventions.md` §Style. No non-`Archive`
declaration used the old names, the blueprint `\lean{...}` tags of chapter 13
cite only the new names, and no compatibility alias is kept.

## Renamed declarations

| Removed | Replacement |
|---|---|
| `MPSTensor.exists_perm_gauge_rotatePhysical_of_isOnSiteSymmetric_blockSum` | `MPSTensor.exists_perm_gauge_rotatePhysical_of_isOnSiteSymmetricUpToPhase` |
| `MPSTensor.exists_perm_unitary_rotatePhysical_of_isOnSiteSymmetric_blockSum` | `MPSTensor.exists_perm_unitary_rotatePhysical_of_isOnSiteSymmetricUpToPhase` |
| `MPSTensor.exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetric_blockSum` | `MPSTensor.exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetricUpToPhase` |
| `MPSTensor.commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric_blockSum` | `MPSTensor.commute_leftPolarPhysicalFactor_of_isOnSiteSymmetricUpToPhase` |
| `MPSTensor.exists_isometricDeformationBlocks_unitary_covariance_of_isOnSiteSymmetric_blockSum` | `MPSTensor.exists_isometricDeformationBlocks_unitary_covariance_of_isOnSiteSymmetricUpToPhase` |
| `MPSTensor.groundSpaceES_toTensorFromBlocks_invariant_of_isOnSiteSymmetric` | `MPSTensor.groundSpaceES_toTensorFromBlocks_invariant_of_isOnSiteSymmetricUpToPhase` |
| `MPSTensor.parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetric_blockSum` | `MPSTensor.parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetricUpToPhase` |
| `MPSTensor.isometricDeformationInteractionES_commute_of_isOnSiteSymmetric_blockSum` | `MPSTensor.isometricDeformationInteractionES_commute_of_isOnSiteSymmetricUpToPhase` |
| `MPSTensor.isometricDeformation_parentHamiltonianES_commute_of_isOnSiteSymmetric_blockSum` | `MPSTensor.isometricDeformation_parentHamiltonianES_commute_of_isOnSiteSymmetricUpToPhase` |
| `MPSTensor.isometricDeformation_openParentHamiltonianES_commute_of_isOnSiteSymmetric_blockSum` | `MPSTensor.isometricDeformation_openParentHamiltonianES_commute_of_isOnSiteSymmetricUpToPhase` |
| `MPSTensor.isometricDeformation_periodicInteractionHamiltonianES_commute_of_isOnSiteSymmetric_blockSum` | `MPSTensor.isometricDeformation_periodicInteractionHamiltonianES_commute_of_isOnSiteSymmetricUpToPhase` |
| `MPSTensor.isometricDeformation_openInteractionHamiltonianES_commute_of_isOnSiteSymmetric_blockSum` | `MPSTensor.isometricDeformation_openInteractionHamiltonianES_commute_of_isOnSiteSymmetricUpToPhase` |

Each replacement has the same conclusion except the two block-permutation
theorems, whose conclusions acquire a unimodular scalar factor. The hypothesis
is weaker: exact symmetry implies symmetry up to a phase by
`MPSTensor.IsOnSiteSymmetric.isOnSiteSymmetricUpToPhase`, so every former use
is recovered by composing with that implication. The mathematical argument is
recorded in `docs/paper-gaps/spc11_isometric_symmetry_unitary_virtual.tex`.
