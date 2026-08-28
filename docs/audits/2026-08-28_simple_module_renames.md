# MPDO simple-module path renames

Issue #7139 removes the stale `Source` qualifier from the active module paths
for MPDO simplicity. No declarations, theorem statements, or proof bodies were
changed.

## Mappings

| Previous module path | Current module path |
|---|---|
| `TNLean/MPS/MPDO/SourceSimpleTensor.lean` | `TNLean/MPS/MPDO/Simple.lean` |
| `TNLean/MPS/MPDO/SourceSimpleScaling.lean` | `TNLean/MPS/MPDO/SimpleScaling.lean` |
| `TNLean/MPS/MPDO/RescalingStableSourceSimple.lean` | `TNLean/MPS/MPDO/RescalingStableSimple.lean` |

All production imports, the generated `TNLean/MPS/MPDO.lean` aggregator, and
current reader-facing references now use the new paths. Apart from the mapping
table above, the old names remain only in
`docs/audits/2026-08-24_degenerate_readings_wave_2.md`, whose statements explicitly
record the paths as they existed during that earlier pass.

## Verification

- `python3 scripts/generate_import_aggregators.py` regenerated 36 aggregators
  covering 995 production modules and updated `TNLean/MPS/MPDO.lean`.
- `python3 scripts/blueprint_lean_sync.py --update-lean-decls` scanned 13,199
  TNLean declarations and 6,637 unique Blueprint declaration references; the
  generated declaration data remained synchronized.
- `python3 scripts/blueprint_lean_sync.py --ci` passed with all 6,658
  theorem-like Blueprint entries synchronized.
- A targeted `lake build` passed for `TNLean.MPS.MPDO.Simple`,
  `TNLean.MPS.MPDO.SimpleScaling`, `TNLean.MPS.MPDO.RescalingStableSimple`,
  `TNLean.MPS.MPDO.BNTBoundaryDecomposition`,
  `TNLean.MPS.MPDO.CPSVExample412NormalizedRFP`, and the generated
  `TNLean.MPS.MPDO` direct importer (9,623 jobs including cached dependencies).
- `lake env lean` then passed separately on the corresponding six source files.
- Searches found no old module name in a non-historical Lean import or current
  reader-facing path reference.
- `git diff --check` passed.
