# Import waypoint retirement and three dead import edges (2026-09-19)

Twelve handwritten modules under `TNLean/` carried no declarations: a copyright
header, a list of imports, and a module docstring. Eleven of them shadowed a
directory of the same name, so the nearest generated ancestor imported both the
handwritten module and every module of that directory again; the twelfth was a
one-import alias with no directory. This is the shape retired on 2026-08-26
(`docs/audits/2026-08-26_spectral_import_waypoint_retirement.md`) and on
2026-08-27 (`docs/audits/2026-08-27_bicfderivation_import_waypoint_retirement.md`).

## Removed and replaced

| Removed | Replacement |
|---|---|
| handwritten `TNLean.MPS.ParentHamiltonian.Martingale` | generated aggregator at the same module path |
| handwritten `TNLean.MPS.CanonicalForm.CyclicSectors` | generated aggregator at the same module path |
| handwritten `TNLean.MPS.CanonicalForm.NormalReduction` | generated aggregator at the same module path |
| handwritten `TNLean.MPS.Periodic.Overlap` | generated aggregator at the same module path |
| handwritten `TNLean.MPS.Periodic.Overlap.SectorMatch` | generated aggregator at the same module path |
| handwritten `TNLean.MPS.Periodic.SectorIrreducibility` | generated aggregator at the same module path |
| handwritten `TNLean.MPS.Periodic.Symmetry` | generated aggregator at the same module path |
| handwritten `TNLean.PEPS.EdgeMiddlePhysical` | generated aggregator at the same module path |
| handwritten `TNLean.PEPS.TorusWindowPeeling` | generated aggregator at the same module path |
| handwritten `TNLean.MPS.MPDO.BiCFDerivation.PairHomogenization` | generated aggregator at the same module path |
| handwritten `TNLean.MPS.MPDO.GSNNCHFourCycleMarkov` | generated aggregator at the same module path |
| handwritten `TNLean.MPS.Periodic.SectorUnitary` | none; its sole import `TNLean.MPS.Periodic.Overlap.GaugePhase` is reached directly |
| `HANDWRITTEN_IMPORT_OWNERSHIP` and its three helper functions in `scripts/generate_import_aggregators.py` | the exception-free coverage rule |

No declaration was removed: a comment-stripped scan of all twelve files returns
no `theorem`, `def`, `structure`, `instance`, `abbrev` or `class` head, and no
non-import command of any kind. No blueprint `\lean{}` payload can name a
module, and no blueprint prose names any of the twelve module paths; the single
textual match on `EdgeMiddlePhysical` is the tag
`TNLean.PEPS.EdgeMiddlePhysicalConfig`, declared in
`TNLean/PEPS/EdgeMiddlePhysical/Basic.lean`.

`TNLean.MPS.Periodic.SectorUnitary` shadowed no directory, so its path is
vacated rather than regenerated. Its only importer was the generated
`TNLean/MPS/Periodic.lean`, which imports `Overlap.GaugePhase` through the
regenerated `Periodic.Overlap` aggregator.

## Closure effects

The eleven regenerated aggregators cover their whole directory, where three of
the handwritten waypoints covered only part of it:
`CyclicSectors` omitted `CornerBridge`; `Periodic.Overlap` omitted
`GaugePhase`, `SectorOverlapTransport` and `SelfOverlapSetup`;
`Overlap.SectorMatch` omitted `Basic`, `CyclicTrace` and `CyclicTransport`.
The omitted modules were already imported directly by the parent umbrella, so
no module gains or loses root reachability. A transitive-closure pass over
every non-Archive import edge after regeneration finds no cycle and no import
of a module that does not exist.

The thirteen handwritten import lines that named a retired waypoint still name
the same module, now a generated aggregator. Re-pointing those importers at the
leaves they actually use is deferred; it changes import closures and must be
build-verified separately.

## Ownership exception

The coverage check of `scripts/generate_import_aggregators.py` deliberately
ignores handwritten reachability. `HANDWRITTEN_IMPORT_OWNERSHIP` was the single
declared exception to that rule: it suppressed the two imports
`TNLean.MPS.ParentHamiltonian.BlockedGroundSpaceTransport` and
`TNLean.MPS.ParentHamiltonian.LocalSupportTransport` from the
`TNLean.MPS.ParentHamiltonian` aggregator, on the ground that the handwritten
`Martingale` waypoint reached them through `Martingale.BlockedGap`.

The exception verifies each edge of that path against the *source* files at the
moment the coverage check runs, before any aggregator is written. With the
waypoint deleted, the first edge has no source file, the delegation fails to
verify, and the generator refuses to write anything, reporting both transport
modules as absent from the frontier. Regenerating was therefore impossible with
the table in place, and the table was removed together with
`delegated_modules`, `source_imported_modules`, `verified_delegated_modules`,
their two call sites, the source-import regular expression, five tests that
exercised only that path, and the documenting paragraph of
`docs/import_structure.md`. The aggregator regains the two direct imports, which
reverses the two-line removal recorded in #6398. The coverage rule is now
exception-free.

Aggregator census after the change: 51 generated files covering 1,265
production modules (was 40 / 1,277).

## Three dead import lines

Three import lines were removed in the same pass:

* `TNLean/MPS/CanonicalForm/SectorComparison/NormalityChain.lean` dropped
  `TNLean.MPS.Chain.BlockedChainFT`;
* `TNLean/MPS/CanonicalForm/SectorComparison/TPPrimitiveReduction.lean` dropped
  `TNLean.MPS.CanonicalForm.CommonPeriodCyclicSectors`;
* `TNLean/MPS/MPDO/PhysicalSupportRestriction.lean` dropped
  `TNLean.MPS.CanonicalForm.ProjectorClosureDecomposition`.

The exclusive cone of each edge was recomputed over the whole import graph,
including the QICLean and Mathlib dependencies, so that no module upstream of
the boundary hides inside a cone. The first cone is
`Chain/{BlockedChainFT, FundamentalTheorem, AlgebraIsomorphism, VirtualInsertion}`,
the second is `CanonicalForm/CommonPeriodCyclicSectors`, and the third is
`CanonicalForm/{ProjectorClosureDecomposition, ProjectorClosure}`. None of the
declarations of those cones is named in any module that loses access. The only
attributes in the cones are two simp lemmas whose head constants are defined in
the cone itself and named nowhere downstream; the cones contain no instance, no
notation, no macro and no simp-set registration.

Measured reverse cones over handwritten modules, before and after the three
removals: `Chain.VirtualInsertion` 446 to 188, `Chain.AlgebraIsomorphism` 364 to
9, `Chain.FundamentalTheorem` 363 to 8, `Chain.BlockedChainFT` 356 to 1,
`CanonicalForm.CommonPeriodCyclicSectors` 356 to 0,
`CanonicalForm.ProjectorClosureDecomposition` 314 to 283,
`CanonicalForm.ProjectorClosure` 315 to 284. Every cone module keeps its
blueprint tags and stays built through the generated aggregators.

## Retained

`docs/counterexamples.md` recorded the `H = -Id` witness for the martingale
positivity step at the retired waypoint; the entry now points at
`TNLean/MPS/ParentHamiltonian/Martingale/AbstractCriterion.lean`, where the
witness is stated in the docstring of the abstract criterion.

The retired `Martingale` docstring carried a twenty-five item inventory of its
directory and a six-step narrative of the martingale argument. The inventory is
what the generated aggregator reproduces automatically. The narrative is owned
by `blueprint/src/chapter/ch13_parent_hamiltonian_spectral_gap_martingale.tex`
and its cyclic-overlap and row-sum companions, which carry the same steps with
their statement labels, so it is dropped rather than relocated.

Dated audit notes that mention a retired path as historical context are left
as written.
