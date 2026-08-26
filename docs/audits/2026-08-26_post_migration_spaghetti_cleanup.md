# Post-migration QICLean/TNLean spaghetti cleanup

Date: 2026-08-26

## Scope and ownership rule

This report records the implementation pass that followed the read-only QICLean/TNLean
spaghetti audit. The governing boundary is now:

- generic matrix-family, Kraus-map, channel, fixed-point, spectral, gauge-normalization, and
  Wielandt support belongs in QICLean;
- MPS/MPDO/PEPS/MPU/QCA statements and bridges involving `GaugeEquiv`, `SameMPV`, blocking,
  overlaps, canonical forms, and parent Hamiltonians remain in TNLean.

`Kraus.mapLM` and `Kraus.mixedMapLM` are the canonical map APIs. The reducible
`Kraus.transferMap` alias remains intentionally available for exact MPS terminology; the removed
compatibility theorem ecosystems must not be recreated.

## Completed cleanup

### Generic ownership

QICLean PR #502 and TNLean PR #7186 completed the generic-ownership wave:

- matrix-family invariant-submodule and irreducible-action infrastructure moved to QICLean;
- Kraus Burnside/span-growth support moved to QICLean;
- projection-triangular trace and word identities moved to QICLean, leaving only the TNLean
  `SameMPV` bridge;
- TP/unital gauge construction, similarity, primitivity, and irreducibility transport moved to
  QICLean, leaving only tensor-network gauge/MPV bridges in TNLean.

### Compatibility surfaces and pass-through declarations

QICLean PRs #503--#505 and TNLean PRs #7189, #7190, and #7192 removed the remaining selected
compatibility surfaces:

- deleted `QICLean.Kraus.TransferChannel` and migrated all TNLean consumers to canonical
  `Kraus.mapLM` results;
- deleted `QICLean.Spectral.MixedTransfer` and migrated QICLean and TNLean to
  `Kraus.mixedMapLM`;
- removed the final exact mixed-gap forwarding theorem whose name advertised the retired API;
- removed verified dead blocking and strong-irreducibility forwards in the ownership wave;
- removed five dead or exact TNLean pass-through declarations in SectorBNT, canonical-form, and
  multi-block APIs, retargeting Lean and Blueprint consumers to their canonical declarations.

Repository-wide live-source searches now find no `TransferChannel`, `Spectral.MixedTransfer`,
`mixedTransferMap`, or `mixedTransferMap₂` production/Blueprint consumers.

### Dependency direction

TNLean PR #7191 repaired three lower-layer ownership inversions while preserving declaration names
and statements:

- overlap-to-gauge recovery now lives in `MPS.SharedInfra.GaugePhase`, below both CanonicalForm
  and FundamentalTheorem;
- sector power-sum eventuality now lives in `MPS.SharedInfra.SectorDecomposition`, below both
  CanonicalForm and FundamentalTheorem;
- RFP-specific commuting-parent-Hamiltonian bridges now live in `MPS.RFP.CommutingBridge`, so
  `ParentHamiltonian.Commuting` no longer imports RFP implementation modules.

TNLean PR #7199 moved the BNT-facing direct-sum selector/separation closure to
`MPS.BNT.DirectSumSelectors`. This removes the direct
`ParentHamiltonian.BNTBlockIntersection -> MPDO.BiCFDerivation.BNTDirectSum` edge while
preserving all sixteen moved theorem names, statements, proofs, and docstrings.

### Witness packaging

TNLean PR #7198 introduced `PreparedBNTBlocks` and
`PreparedBNTBlocks.IsWeightNormalized`, with bundled collapsed, existential,
dimension-preserving, and exact reconstruction adapters. The canonical-form bridge now passes one
record rather than parallel dependent arguments. Existing public theorem statements and the long
coordinate reconstruction proof were left unchanged.

## Verification

Each implementation wave received targeted builds before review. Final merged-tree verification
included:

- full QICLean build (9,332 jobs);
- full TNLean build (10,387 jobs; completed incrementally after the command timeout);
- QICLean Blueprint synchronization: 2,621 / 2,621 theorem-like entries;
- TNLean Blueprint synchronization and declaration resolution;
- generated-import freshness checks;
- module-policy and style checks;
- proof-integrity checks and `git diff --check`;
- import-cycle and forbidden-edge searches;
- no new `sorry` or `admit` in changed production Lean files.

The unrelated untracked `docs/tenkz/` directory was not modified.

## Deliberately deferred high-churn work

The following findings remain valid but were intentionally excluded from this reviewable cleanup
pass:

1. **PEPS numbered continuation chains.** Renaming and regrouping the `Recovery*`,
   `CoarseThreeSite*`, `TorusWindowChain*`, and `UnionInjectivityOverlap*` families touches a large
   import surface without changing mathematics. This should be a dedicated organizational project.
2. **Full transitive MPDO selector extraction.** `MPS.BNT.DirectSumSelectors` still consumes
   foundational selector/direct-sum infrastructure under `MPDO.BiCFDerivation`. Eliminating that
   transitive cone requires relocating several large modules (`Core`, `Selectors`,
   `DirectSumInput`, `DirectSumGroundSpace`, and `DirectSumUniqueness`) and needs a separate audit.
3. **Larger dependent witness structures.** `SectorBNTMatch` and cyclic-sector compression output
   still use large nested existential payloads. They are higher risk than `PreparedBNTBlocks`
   because they interact with coordinate transport, equivalences, and literal ambient reindexing.
4. **Proof-hotspot decomposition.** The large recursive/projector, prepared reconstruction,
   unitary-gauge, cyclic-cut, and PEPS geometry proofs remain substantive mathematics. They should
   be split only after introducing stable intermediate lemmas, not by tactic golfing.
5. **Broad blocking alias retirement.** Deeply used `MPSTensor` blocking terminology remains.
   Retiring it requires a dedicated consumer migration; only verified unused exact forwards were
   removed here.
6. **Large domain modules.** `StringOrderAux`, `CanonicalForm/NormalReduction/TPGauge`,
   quantitative parent-Hamiltonian proofs, and selected MPDO/RFP proofs remain candidates for
   conceptual splitting, but no low-risk split was bundled into this pass.

## Current architectural verdict

The principal post-migration debt is no longer duplicated generic channel mathematics. The selected
generic results have one QICLean owner, TNLean uses canonical map APIs, the audited direct layer
inversions are repaired, and repeated prepared-block witness data has a typed package. Remaining
work is predominantly high-churn organization and decomposition of genuine tensor-network proofs.
