# PR #7190 pass-through retirement inventory

Date: 2026-08-26

PR #7190 removed four public declarations that merely forwarded to an existing theorem,
projected a structure field, or preserved a deprecated exact alias. All live non-`Archive`
consumers and Blueprint references were migrated before deletion.

| Removed declaration | Canonical replacement |
|---|---|
| `MPSTensor.gaugeEquiv_toTensorFromBlocks_implies_sameMPV` | `MPSTensor.GaugeEquiv.sameMPV` |
| `MPSTensor.IsBNTCanonicalForm.weight_unit_exists_of_struct` | `MPSTensor.IsBNTCanonicalForm.weight_unit_exists` |
| `MPSTensor.IsBNTCanonicalForm.coeff_not_eventually_zero` | `MPSTensor.SectorDecomposition.coeff_not_eventually_zero`, now owned by `TNLean.MPS.SharedInfra.SectorDecomposition` |
| `SectorBNT.Examples.singletonDecomp` | `MPSTensor.singleSectorDecomposition` |

The private helper `cyclic_projection_nonzero_of_sum_one` was also removed after its proof was
written directly at the sole use site. As a private declaration it is not a public compatibility
endpoint.

This inventory supplies the audit trail required by `docs/project_conventions.md` for retiring
public pass-through declarations without transition aliases.
