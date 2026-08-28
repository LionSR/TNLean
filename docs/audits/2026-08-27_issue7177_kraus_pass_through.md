# Issue #7177: Kraus pass-through migration inventory

Audited at TNLean `a07808833b84eab82fbdba6e47c3e0f826443821`, with QICLean pinned at
`a8347e6f9f97f331c51ec911ca27b8fc8d46a783`.

PR #7177 removed the following TNLean pass-through declarations after migrating
their non-Archive consumers and Blueprint tags to the existing generic owners.
This table supplies the per-declaration inventory required by the repository's
pass-through exception.

| Removed declaration | Replacement |
|---|---|
| `MPSTensor.transferMap_conjTranspose_eq_adjoint` | `Kraus.mapLM_conjTranspose_eq_adjoint` |
| `MPSTensor.transferMap_adjoint_eq_adjointMapLM` | `Kraus.adjointMapLM_apply` via `Kraus.mapLM_conjTranspose_eq_adjoint` |
| `MPSTensor.transferMap_adjoint_apply_eq_adjointMap` | `Kraus.adjointMapLM_apply` via `Kraus.mapLM_conjTranspose_eq_adjoint` |
| `MPSTensor.lowerZero_implies_invariance` | `Kraus.lowerZero_implies_invariance` |
| `MPSTensor.isUnit_peripheral_eigenvector` | `Kraus.isUnit_peripheral_eigenvector` |
| `MPSTensor.peripheralEigenvalues_pow_mem_of_irreducible_unital_of_adjoint_fixedPoint` | `Kraus.peripheralEigenvalues_pow_mem_of_irreducible_unital_of_adjoint_fixedPoint` |
| `MPSTensor.peripheral_isRootOfUnity_of_irreducible_unital_of_adjoint_fixedPoint` | `Kraus.peripheral_isRootOfUnity_of_irreducible_unital_of_adjoint_fixedPoint` |
| `MPSTensor.peripheralEigenvalues_mul_mem_of_irreducible_unital_of_adjoint_fixedPoint` | `Kraus.peripheralEigenvalues_mul_mem_of_irreducible_unital_of_adjoint_fixedPoint` |
| `MPSTensor.peripheralEigenvalues_eq_range_primitiveRoot` | `Kraus.peripheralEigenvalues_eq_range_primitiveRoot` |
| `MPSTensor.isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor` | `Kraus.isIrreducibleMap_mapLM_conjTranspose` after `Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily` |
| `MPSTensor.isIrreducibleTensor_of_isIrreducibleMap_conjTranspose` | `Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM` after `Kraus.isIrreducibleMap_mapLM_conjTranspose_iff` |
| `MPSTensor.lowerZero_of_posSemidef_fixedPoint` | `Kraus.lowerZero_of_posSemidef_fixedPoint` |
| `MPSTensor.invariance_implies_lowerZero` | `Kraus.invariance_implies_lowerZero` |
| `MPSTensor.isIrreducibleCP_transferMap_of_isIrreducibleTensor` | `Kraus.isIrreducibleMap_transferMap_of_isIrreducibleFamily` |
| `MPSTensor.isIrreducibleTensor_of_isIrreducibleMap` | `Kraus.isIrreducibleFamily_of_isIrreducibleMap_transferMap` |
| `MPSTensor.self_correlation_persists` | `Kraus.self_correlation_persists` |
| `MPSTensor.transferMap_conjTranspose` | `Kraus.map_conjTranspose` |
| `MPSTensor.transferMap_pow_smul_eigenvector` | `Module.End.pow_apply_of_mem_eigenspace` (Mathlib) |
| `MPSTensor.trace_eigenvector_eq_zero` | `Kraus.trace_eigenvector_eq_zero` |
| `MPSTensor.posSemidef_pow_fixedPoint_unique_of_isPrimitivePaper` | `Kraus.posSemidef_pow_fixedPoint_unique` |
| `MPSTensor.transferMap_pow_apply_eq_sum` | `Kraus.transferMap_pow_apply'` |
| `MPSTensor.IsPrimitiveMPS.transferMap_isChannel` | `Kraus.isChannel_transferMap _ hP.norm` at the former use site |
| `MPSTensor.isIrreducibleMap_of_isIrreducibleTensor` | `Kraus.isIrreducibleMap_transferMap_of_isIrreducibleFamily` |

The three deprecated cyclic-projector compatibility aliases removed in the same
PR were already marked for retirement and are outside this pass-through
inventory.
