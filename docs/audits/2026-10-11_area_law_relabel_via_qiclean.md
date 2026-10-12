# Area-law site relabelling from QICLean region covariance

Date: 2026-10-11. PR: refactor(PEPS/AreaLaw): derive site relabelling from
QICLean region covariance.

LionSR/QICLean#711 proves, for an arbitrary finite set of sites with a
dimension per site, that a region-preserving bijection of sites and basis
labels transports the regional state by conjugation and leaves the regional
entropy unchanged (`Entropy.regionState_relabel`,
`Entropy.regionEntropy_relabel` in `QICLean/Entropy/RegionCovariance.lean`).
LionSR/QICLean#780 adds the matching norm statement
`Entropy.norm_relabelVector`. `TNLean/PEPS/AreaLaw/RegionalReindex.lean` now
reads these at constant local dimension `q` with identity basis bijections,
through `reducedState_eq_regionState` and `regionalEntropy_eq_regionEntropy`.
The statements of `reducedState_relabel`, `regionalEntropy_relabel` and
`norm_relabelState` are unchanged; `regionConfigurationEquiv` and
`relabelState` keep their names and types and are now defined as the
corresponding QICLean constructions.

## Removed declarations and replacements

| Removed (TNLean) | Replacement (QICLean) |
|---|---|
| `TNLean.PEPS.AreaLaw.configurationSiteEquiv` | `Entropy.siteConfigurationEquiv e (fun _ ↦ Equiv.refl _)` |
| `TNLean.PEPS.AreaLaw.complementConfigurationEquiv` | `Entropy.complementConfigurationEquiv A A' e hA (fun _ ↦ Equiv.refl _)` |
| `configurationSplit_symm_pullback` (private) | absorbed into `Entropy.regionState_relabel` |

No open pull request used any of the removed names when this PR was opened.
The blueprint tags in `ch24_peps_area_law_regional_reindex.tex` were updated.
