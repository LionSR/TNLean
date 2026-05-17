# 2026-05-17 — open-issues audit

Audit pass over the 134 then-open issues in `LionSR/TNLean`, walking each one
against the current `main` (commit `8adb379`) to identify stale, completed, or
superseded tickets and to consolidate the Phase 7 cleanup surface.

## Closures

| # | Title | Reason | Verification |
|---|---|---|---|
| 1705 | Phase 6a: port `rfp_bnt_structural` to `IsBNTCanonicalForm` | completed | `TNLean/MPS/RFP/StructuralForm.lean:260` now takes `(P, hP)` and returns `hP.basis_injective`; PR #1711 |
| 1708 | Phase 6d: update `IsCanonicalFormBNT` doc refs in `PiAlgebra` | completed | `CanonicalFormSep.lean:602`, `CanonicalFormSepAux.lean:230,311` carry updated docstrings; PR #1715 |
| 1394 | `[aw] Docs & Blueprint Sync failed` | completed | embedded expiry `2026-05-13` has passed; new failures generate fresh issues |
| 1498 | Tracking: Non-periodic FT — discharge CPSV16 hypotheses | superseded (#1685) | `Full.lean`, `BlockDiagonalCommutant.lean`, `CommonPrimitiveProportionalData.lean` all deleted in #1738 |
| 1499 | `BiCFDerivation`: identity-padded homogeneous pair-span | superseded (#1685) | child of #1498; route retired in #1738 |
| 1500 | `SectorComparison`: fixed-length block-injective span | superseded (#1685) | target file `BlockDiagonalCommutant.lean:697` deleted |
| 1501 | `CanonicalForm`: derive `CommonPrimitiveBNTCoverHypotheses` | superseded (#1685) | target file `CommonPrimitiveProportionalData.lean` deleted; replaced by `PaperBNT/Fundamental` |
| 1543 | `Wielandt`: `isInjective_blockTensor_of_isNormal` | superseded (#1685) | "only remaining anchor on critical path of #1498"; #1498 itself retired |
| 1559 | Tracking: paper-faithful proportional MPV FT | superseded (#1685) | `Full/{NondecayingOverlap,ProportionalScalar,ProportionalExpansion,ProportionalDominant}.lean` deleted; replacement on `PaperBNT/` |

All closures use `state_reason = not_planned` for the superseded set and
`state_reason = completed` for the three already-done ones. Closures are
reversible if any of the underlying mathematics turns out to still be needed
on the paper-faithful `PaperBNT/` surface.

## New issue

- **#1756** — Phase 7 final: delete `IsCanonicalFormBNT` structure from
  `BNT/Construction.lean`. Concrete, well-scoped deletion (~200 LoC net
  negative): the structure definition, its four forgetful projections
  (`toHasInjectiveBlocks`, `toIsLeftCanonicalBlockFamily`,
  `toHasStrictOrderedNonzeroWeights`, `toHasNormalizedSelfOverlap`), the
  `ofSeparatedData` reconstructor, the `_of_distinct_dims` corollary, plus
  two stray docstring references in `SectorDecomposition.lean:425` and
  `PaperBNT/DominantMatch.lean:59`. The `lake build` invariant is that
  `rg -n 'IsCanonicalFormBNT' TNLean/` returns zero hits afterwards.

## Linking comments

- **#1685** (clean-slate FT umbrella) — full status snapshot of Phases 1–7 and
  the still-open Phase 7 sub-issues (#1697, #1734, #1735, #1739, #1741, #1742,
  #1746, #1749, #1751, #1753, #1755, #1662, #1663, #1651, #1656, #1756).
- **#1170** (older FT/BNT/Wielandt cleanup tracker) — flagged that the FT/BNT
  part has migrated to #1685; remains useful for the Wielandt / cross-cutting
  refactor / blueprint-gap content it also bundles.
- **#448**, **#450**, **#872**, **#873** — flagged that their target files
  (`MPS/Periodic/Overlap/{SelfOverlap,Dichotomy,Case2,Case3}.lean`) are now
  orphans (still on disk, dropped from `TNLean.lean` in #1740). Whether the
  named sorrys should be discharged depends on the retarget-or-delete
  decision in #1741, so the bots should not autofix against those files
  until then.

## Left open intentionally

- All paper-level umbrellas (#11, #20, #21, #22, #128, #190, #232, #236, #237,
  #239, #619, #903, #992, #995, #996, #998, #1404, #1447) — they are
  long-lived trackers, not work items.
- Daily standups (#589, #601, #602, #791, #1496) — dated historical records;
  closure pattern is owner-driven.
- Audit chapters with concrete deliverables (#317, #318, #322, #328, #335,
  #1613, #1616, #1618, #1628, #1632) — these audits are still actionable
  against current `main`.
- The `[aw] No-Op Runs` index (#1208) — self-managed by github-actions; the
  body says "Do not close this issue manually."
- Single-statement formalization issues with files still in the build
  surface (#460, #870, #905, #952, #1117, #1475, etc.) — these track honest
  remaining sorrys in live modules.
- Bug / `bug` label issues (#1659, #1565) — bug investigations not in scope
  for a staleness pass.

## Numbers

- Before: 134 open
- Closed: 9 (3 completed + 6 superseded — list above)
- Opened: 1 (#1756)
- After: 126 open
