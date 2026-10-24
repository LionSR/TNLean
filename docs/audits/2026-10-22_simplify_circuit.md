# Simplification pass: TNLean/Circuit

Date: 2026-10-22. PR: #9927.

A behaviour-preserving simplification of TNLean/Circuit. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `rectangularKrausMap_rectKronecker_finKronecker` | `TNLean/Circuit/Channel/Conversion.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `blockSites_symm_apply` | `TNLean/Circuit/Channel/SiteBlocking.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `mem_supportedOperators` | `TNLean/Circuit/Composition.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `ctrlOp_diagonal` | `TNLean/Circuit/Gates/Controlled.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `twoLevel_submatrix` | `TNLean/Circuit/Gates/TwoLevel.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `lightCone_mono` | `TNLean/Circuit/Geometry.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `subset_lightCone` | `TNLean/Circuit/Geometry.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `openBond_nonempty` | `TNLean/Circuit/Geometry.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `expect_zero` | `TNLean/Circuit/LocalCircuit.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `expect_productVector_finKronecker` | `TNLean/Circuit/LocalCircuit.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `exists_ghzSite` (private) | `TNLean/Circuit/Measurement/GHZ.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `finset_prod` | `TNLean/Circuit/PairProduct.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `embedOp_finKronecker` | `TNLean/Circuit/SiteEmbedding.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `inputCfg_injective` | `TNLean/Circuit/SiteEmbedding.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `one` | `TNLean/Circuit/WindowProduct.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
