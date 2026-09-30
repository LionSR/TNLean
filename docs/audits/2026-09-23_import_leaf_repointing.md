# Re-pointing handwritten imports at retired-aggregator leaves (2026-09-23)

Follow-up to the waypoint retirement recorded in
`docs/audits/2026-09-19_import_waypoint_retirement_and_dead_edges.md` and
tracked as issue #7874. The eleven retired waypoints were regenerated as
directory aggregators; the handwritten import lines elsewhere in the tree that
still named one of them therefore pulled in the whole directory instead of the
leaf module(s) actually used. This pass re-points those lines at the leaves.

The issue body says thirteen handwritten lines; a scan of every handwritten
TNLean module against the generated aggregators finds exactly twelve, all among
the eleven retired waypoint paths. No handwritten module imports any of the
other generated aggregators. Three of the twelve lines are deletions rather
than re-pointings, so nine lines are re-pointed.

## What changed

For each line the replacement was chosen by an exclusive-cone name scan: the
leaf modules of the aggregator's directory whose declarations the importing
file actually names. Instances and `simp` attributes were checked separately,
since they are used without being named.

| File | Old import | New import(s) |
|---|---|---|
| `TNLean/MPS/CanonicalForm/BNTGrouping.lean` | `CanonicalForm.NormalReduction` | none (cone-dead; the line is deleted) |
| `TNLean/MPS/CanonicalForm/SectorComparison/TPPrimitiveReduction.lean` | `CanonicalForm.NormalReduction` | `NormalReduction.TPGauge` (provides `exists_tp_gauge_from_arbitrary`) |
| `TNLean/MPS/CanonicalForm/SectorComparison/TPPrimitiveReduction.lean` | `CanonicalForm.CyclicSectors` | none (cone-dead; the line is deleted) |
| `TNLean/MPS/CanonicalForm/SectorComparison/CyclicSectorDecomposition.lean` | `Periodic.SectorIrreducibility` | `Periodic.SectorIrreducibility.HLift` (provides `cyclic_projection_mul_left`, `cyclic_projection_mul_right`, `isIrreducibleOnCorner_of_cyclic_decomp_mps`) |
| `TNLean/MPS/Periodic/FundamentalTheorem.lean` | `Periodic.Overlap` | `Periodic.Overlap.Dichotomy` (provides `periodicOverlapDichotomy`), `Periodic.Overlap.SelfOverlap` (provides `periodicSelfOverlap_tendsto`) |
| `TNLean/MPS/Periodic/Overlap/Dichotomy.lean` | `Periodic.Overlap.SectorMatch` | `Periodic.Overlap.SectorMatch.Consequences` (provides `periodicOverlap_gaugeEquiv_of_sector_match`, `periodicOverlap_tendsto_zero_of_ne_dim`; `Contraction` is reached transitively through it) |
| `TNLean/MPS/Periodic/Overlap/SelfOverlapSetup.lean` | `CanonicalForm.CyclicSectors` | none (closure-neutral; `CornerBridge`, `CommonSectorData` and `CyclicSectorRelation` keep the cone reachable) |
| `TNLean/MPS/Periodic/Overlap/SelfOverlapSetup.lean` | `Periodic.SectorIrreducibility` | none (closure-neutral; the `HLift` cone is reached through `CommonSectorData`) |
| `TNLean/MPS/Periodic/SectorIrreducibility/ProjectionOrtho.lean` | `CanonicalForm.CyclicSectors` | `CanonicalForm.CyclicSectors.FixedAdjoint` (provides `commutes_letters_of_adjoint_fixed_projection`) |
| `TNLean/MPS/Periodic/ProjectiveRep.lean` | `Periodic.Symmetry` | `MPS.Symmetry.Defs` (provides `twistedTensor`; the file never names a `Periodic.Symmetry` leaf) |
| `TNLean/PEPS/InsertionAlgebra.lean` | `PEPS.EdgeMiddlePhysical` | `PEPS.EdgeMiddlePhysical.Basic` |
| `TNLean/PEPS/InsertionRealization.lean` | `PEPS.EdgeMiddlePhysical` | `PEPS.EdgeMiddlePhysical.Basic` |

## Deviations from the survey table

Two points in the 2026-09-21 leaf table did not survive a name scan and were
handled on the evidence of the scan rather than the table.

- `Periodic/Overlap/Dichotomy.lean`. The table lists only
  `SectorMatch.Consequences`. A raw scan also matches
  `sectorTensor_proportional_of_blockedMatch` from `SectorMatch.Contraction`,
  but that match is inside a comment, not a use. `Consequences` itself imports
  `Contraction`, so the single-leaf replacement the table gives is correct and
  is what was applied.
- The two `PEPS` files both take `Basic` only. Neither file names any
  `KernelDescent` declaration. `TNLean/PEPS/EdgeGaugeFamily.lean` projects
  `hA.edgeBlockedThreeSiteInjective` and `hB.edgeBlockedThreeSiteInjective` off
  `IsVertexInjective` hypotheses, and that dot-notation resolves to the
  declaration `IsVertexInjective.edgeBlockedThreeSiteInjective` in
  `EdgeMiddlePhysical/KernelDescent.lean`. Instead of retaining the full
  `KernelDescent` import in `InsertionAlgebra.lean` as a transitive route,
  `EdgeGaugeFamily.lean` imports `EdgeMiddlePhysical.KernelDescent` directly.
  Both `InsertionAlgebra.lean` and `InsertionRealization.lean` are thus pruned
  to `Basic` alone.

`Periodic/ProjectiveRep.lean` was the one line the survey flagged as not a
plain leaf re-pointing: the aggregator import was the file's only route to
`twistedTensor`, and no `Periodic.Symmetry` leaf is named. It is re-pointed at
`MPS.Symmetry.Defs`, the actual home of `twistedTensor`. The nearby
`cor_4_1_physical_symmetry_zgauge_explicit` of `Periodic/Symmetry/Corollary41`
is mentioned only in the module docstring, never applied, so no
`Periodic.Symmetry` leaf is needed.

## Checked

- `python3 scripts/check_forbidden_lean_tokens.py` — clean.
- `python3 scripts/generate_import_aggregators.py --check` — current.
- `python3 scripts/check_numbered_lean_files.py` — no new violations.
- `git diff origin/main --check` — clean.
- `~/bin/lake340.sh build` of all ten edited modules, then of every module
  that imports one of them directly — both builds completed successfully with
  the Mathlib standard linter set enabled.

An import edge is proved only by the root build in CI; the module-target
builds above establish that each edited file and its direct importers still
elaborate, and the root build on the pull request is the remaining witness.

## Retained

The generated aggregators themselves are unchanged; only handwritten importers
moved. No declaration was added, removed or renamed, so no blueprint `\lean{}`
tag moved and the faithfulness rule is not engaged. Both `InsertionAlgebra.lean`
and `InsertionRealization.lean` drop `KernelDescent` in favor of `Basic` alone,
with `EdgeGaugeFamily.lean` importing `KernelDescent` directly for its
`IsVertexInjective.edgeBlockedThreeSiteInjective` dot-projection.
