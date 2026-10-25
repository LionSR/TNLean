# Simplification pass: TNLean/Lattice

Date: 2026-10-22. PR: #9923.

A behaviour-preserving simplification of TNLean/Lattice. No theorem statement used outside
the edited files changes. Following `docs/project_conventions.md`, the removed
declarations and their replacements are recorded here; none was kept as a deprecated
alias, none is cited by a blueprint `\lean{...}` tag, and every remaining use was
migrated to the replacement.

## Removed declarations and replacements

| Removed | File | Replacement |
|---|---|---|
| `memCongr_tmul_heq` (private) | `TNLean/Lattice/Compression/SourceInputSchmidtFrames.lean` | `TNLean.Lattice.PartyCircuit.Layout.memCongr_tmul_heq` |
| `transport_append` (private) | `TNLean/Lattice/Compression/SourcePreparationCoordinates.lean` | `TNLean.Lattice.PartyCircuit.Layout.memCongr_append_tmul` |
| `piSubtypeSplit_symm_apply_right` | `TNLean/Lattice/Compression/WholeGroupContraction.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `partialNormSq_nonneg` | `TNLean/Lattice/Compression/WholeGroupContraction.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `memCongr_apply_heq` (private) | `TNLean/Lattice/PartyCircuit/EffectCircuitError.lean` | `TNLean.Lattice.PartyCircuit.Layout.memCongr_apply_heq` |
| `stackAppIso_final` | `TNLean/Lattice/PartyCircuit/PartyChain.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `gateIso_nil` | `TNLean/Lattice/PartyCircuit/PartyLayout.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `gateIso_cons_clm` | `TNLean/Lattice/PartyCircuit/PartyLayout.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
| `univ_map_pairOwner` | `TNLean/Lattice/PartyCircuit/WordOriginalCircuit.lean` | None: no remaining use in `TNLean/`, `TNLeanTest/`, `scripts/`, `blueprint/` or `docs/` |
