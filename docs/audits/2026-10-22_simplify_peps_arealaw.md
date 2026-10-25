# Simplification pass: TNLean/PEPS/AreaLaw

Date: 2026-10-22. PR: #9965.

A behaviour-preserving simplification of TNLean/PEPS/AreaLaw. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `sqrt_rpow_neg_two_mul'` (private) | `TNLean/PEPS/AreaLaw/AmplificationProof.lean` | `TNLean.PEPS.AreaLaw.sqrt_rpow_neg_two_mul` |
| `mem_unitBox_self` | `TNLean/PEPS/AreaLaw/Geometry/BirthSeparationAngular.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `isQuarterSectorial_univ` | `TNLean/PEPS/AreaLaw/Geometry/BirthSeparationAngular.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `isQuarterSectorial_empty` | `TNLean/PEPS/AreaLaw/Geometry/BirthSeparationAngular.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `mem_beltAtom_add_iff` | `TNLean/PEPS/AreaLaw/Geometry/BirthSeparationAtoms.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `scaleHomeomorph_apply` (private) | `TNLean/PEPS/AreaLaw/Geometry/BirthSeparationStar.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `smul_mem_repairFanCone_iff` | `TNLean/PEPS/AreaLaw/Geometry/RepairFanCones.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `integral_etaOld_rpow_nonneg` | `TNLean/PEPS/AreaLaw/Scan/EnergyBalance.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `integral_etaNew_rpow_nonneg` | `TNLean/PEPS/AreaLaw/Scan/EnergyBalance.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `termEnergy_nonneg` | `TNLean/PEPS/AreaLaw/Scan/EnergyBalance.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
