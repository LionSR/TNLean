# Simplification pass: the smaller TNLean/PEPS subdirectories

Date: 2026-10-22. PR: #9962.

A behaviour-preserving simplification of the smaller TNLean/PEPS subdirectories. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `mem_blue_or_complement_of_not_mem_red` | `TNLean/PEPS/RegionBlock/CoarseThreeSiteCoherentFrame.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `twoBlockScalarProportional_unique` | `TNLean/PEPS/RegionBlock/ProportionalityFromAbsorbed.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `ThreeBlockGeometry.isRegionBoundaryEdge_red_of_host` | `TNLean/PEPS/RegionBlock/UnionInjectivityGeneral2.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `isP0OuterEdge_both_not_mem_R₂` | `TNLean/PEPS/RegionBlock/UnionInjectivityOverlap3.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `isOverlapCrossingEdge_both_mem_R₁` | `TNLean/PEPS/RegionBlock/UnionInjectivityOverlapSetup.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
