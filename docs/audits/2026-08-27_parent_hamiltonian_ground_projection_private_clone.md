# Parent-Hamiltonian ground-projection private clone (2026-08-27)

The helper establishing that a local ground space admits an orthogonal
projection was declared `private` twice, with byte-identical statements and
proofs, in two modules one of which imports the other. The copy in the
importing module has been removed and the surviving copy promoted to a public,
convention-named theorem so that the local-instance attribute in both modules
resolves to a single owner.

| Removed declaration | Replacement |
| --- | --- |
| `MPSTensor.groundSpaceESHasOrthogonalProjection` (private, `TNLean/MPS/ParentHamiltonian/Martingale/C3Threshold.lean`) | `MPSTensor.groundSpaceES_hasOrthogonalProjection` (`TNLean/MPS/ParentHamiltonian/FNWContraction.lean`), reached through the existing import of that module |
| `MPSTensor.groundSpaceESHasOrthogonalProjection` (private, `TNLean/MPS/ParentHamiltonian/FNWContraction.lean`) | `MPSTensor.groundSpaceES_hasOrthogonalProjection` (same module, promoted and renamed to the underscore-separated theorem convention) |

Both modules keep their `attribute [local instance]` line, now naming the
single surviving theorem. The attribute is what keeps the star projection of
a local ground space cheap to elaborate in the operator-norm estimates of
either module, so neither line may be dropped.

## Convention

The pass-through exception at `docs/project_conventions.md` §Style applies. No
`@[deprecated] alias` is warranted: both removed names were `private` and so
had no surface outside their own modules, and no Blueprint `\lean{...}` tag
names either. The precedent is
`docs/audits/2026-08-27_mpdo_sitewise_physical_matrix_private_clone.md`, which
resolved the same shape by giving the duplicated helper one owner.
