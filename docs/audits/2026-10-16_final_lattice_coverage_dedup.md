# Final lattice coverage at an empty generation

This note records the public theorem and module removed from the area-law repair geometry. It is
the audit note required by `docs/project_conventions.md` §Style. Nothing outside `Archive`
used the removed theorem, and no blueprint `\lean{...}` tag cites it after this change. The blueprint
entry `thm:area_law_repair_final_lattice_cover_empty` was removed with it, since no `\uses` list
referred to it. No open pull request touches the removed module, and no compatibility alias is
kept.

## Removed declarations

| Removed | Replacement |
|---|---|
| `TNLean.PEPS.AreaLaw.Geometry.RepairMetricHypotheses.lattice_mem_final_or_terminal_of_isEmpty` (module `TNLean.PEPS.AreaLaw.Geometry.RepairFinalLatticeCoverage`) | `TNLean.PEPS.AreaLaw.Geometry.RepairMetricHypotheses.lattice_mem_terminal_or_unique_final_of_isEmpty` (module `TNLean.PEPS.AreaLaw.Geometry.RepairFinalLatticePartition`) |

The replacement has the same hypotheses: the metric hypotheses, `1 ≤ S_*`, a positive boundary
and an empty generation `N`. Its conclusion is stronger. It places every lattice point in the
terminal interiors or in exactly one final region, while the removed theorem gave only the
covering. The source is the area-law manuscript, `10-geometry.tex`, lines 393–417 and 545–561.
