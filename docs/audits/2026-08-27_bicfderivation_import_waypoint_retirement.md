# BiCF derivation import waypoint retirement (2026-08-27)

`TNLean/MPS/MPDO/BiCFDerivation.lean` carried no declarations: a header, one
import (`BiCFDerivation.DiagonalRestrictionCounterexample`), and a module
docstring listing the sub-modules of the same-named directory.

Unlike the three waypoints retired on 2026-08-26
(`docs/audits/2026-08-26_spectral_import_waypoint_retirement.md`), this path is
**not vacated**. A directory `TNLean/MPS/MPDO/BiCFDerivation/` exists, so
`scripts/generate_import_aggregators.py` re-creates a module at the same path,
now the standard generated directory aggregator: a nine-line generated header
followed by the thirteen sub-module imports.

| Removed | Replacement |
|---|---|
| handwritten `TNLean.MPS.MPDO.BiCFDerivation` (declaration-free waypoint) | generated aggregator at the same module path |

No declaration was removed, and the import closure is unchanged: the only
importer of the waypoint was the generated aggregator `TNLean/MPS/MPDO.lean`,
which already imported all thirteen sub-modules directly. Those thirteen direct
imports are now covered by the new directory aggregator and drop out of
`TNLean/MPS/MPDO.lean`; every other importer in the tree names a sub-module, not
the waypoint.

Two things are deliberately dropped rather than relocated.

* The docstring inventory was stale: it listed nine sub-modules and omitted
  `Blocking`, `PairHomogenization.Algebra`, `PairHomogenization.BurnsideJacobson`,
  and `PairHomogenization.Span`. It was not moved into
  `BiCFDerivation/Basic.lean`, which is itself a declaration-free module with
  its own stale three-item list; relocating the index there would manufacture
  new drift.
* The docstring's deliberate "lighter criterion layer" import restriction — the
  waypoint imported only the obstruction and criterion layer, not the direct-sum
  uniqueness or BNT block-separation files — has no consumer. The generated
  aggregator covers the whole directory, which is what `TNLean/MPS/MPDO.lean`
  already did.

The `## References` block loses nothing: `arXiv:1606.00608, lines 340--345` and
the David--Perez-Garcia--Schuch--Wolf direct-sum decomposition citation already
appear in `BiCFDerivation/Core.lean`, `BiCFDerivation/Selectors.lean`, and
`BiCFDerivation/BNTDirectSum.lean`.

Aggregator census after the change: 36 generated files covering 995 production
modules (was 35 / 996).

Deferred: `TNLean/MPS/MPDO/BiCFDerivation/Basic.lean` is the same shape — 23
lines, zero declarations, stale docstring — differing only in having one real
importer (`BiCFDerivation/DiagonalRestrictionCounterexample.lean`). It is left
for a separate change.
