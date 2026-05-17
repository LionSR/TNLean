# 2026-05-17 — open-issues audit

Audit pass over the 134 then-open issues in `LionSR/TNLean`, walking each one
against the current `main` (commit `8adb379`) to identify stale, completed, or
superseded tickets and to consolidate the Phase 7 cleanup surface. Extended
in a second pass with disk-level findings (orphan modules, large files) and
forward-looking projections from issue-creation patterns.

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

## New issues opened

- **#1756** — Phase 7 final: delete `IsCanonicalFormBNT` structure from
  `BNT/Construction.lean`. Concrete, well-scoped deletion (~200 LoC net
  negative): the structure definition, its four forgetful projections
  (`toHasInjectiveBlocks`, `toIsLeftCanonicalBlockFamily`,
  `toHasStrictOrderedNonzeroWeights`, `toHasNormalizedSelfOverlap`), the
  `ofSeparatedData` reconstructor, the `_of_distinct_dims` corollary, plus
  two stray docstring references in `SectorDecomposition.lean:425` and
  `PaperBNT/DominantMatch.lean:59`. The `lake build` invariant is that
  `rg -n 'IsCanonicalFormBNT' TNLean/` returns zero hits afterwards.
- **#1765** — retire 605 LoC of uncatalogued orphan modules
  (`CornerBridge.lean`, `CommonPeriodCyclicSectors.lean`,
  `PhysicalReindexTransport.lean`, `KrausAdjointSetup.lean`,
  `SectorComparison.lean` aggregator, `Resolvent.lean`). Found by a
  transitive-reachability scan from `TNLean.lean`; not covered by
  #1741 / #1742. Five of the six are pulled into the dead island only by
  retired-route files and should ride the same PR.
- **#1766** — preemptive split of
  `PaperBNT/ProportionalMatch.lean` (997 LoC at clean section boundaries at
  lines 692 / 721 / 832 / 959). The file is the largest active PaperBNT
  module and is in the top-band of recent commit churn; splitting before it
  crosses 1500 LoC keeps reload cost manageable.

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
- **#1741** — orphan LoC accounting for the `MPS/Periodic/{Overlap,Symmetry,...}`
  subtrees (~3,776 LoC across 15 files; ~1,500 carry live `sorry` markers).
  Two additional orphans (`CornerBridge.lean`, `SharedInfra/KrausAdjointSetup.lean`)
  are only pulled in by this island and should ride the same retirement PR.
- **#1742** — orphan LoC accounting for `MPS/CanonicalForm/SectorComparison/`
  subtree (~5,178 LoC across 15 files); three additional orphans
  (`SectorComparison.lean` aggregator, `CommonPeriodCyclicSectors.lean`,
  `Core/PhysicalReindexTransport.lean`) ride the same boundary.

## Disk-level findings (deeper pass)

### Total dead code: 9,559 LoC across 36 orphan files

Transitive-reachability scan from `TNLean.lean`:

```
   846 LoC  TNLean/MPS/Periodic/                     ← #1741
   950 LoC  TNLean/MPS/Periodic/Symmetry/            ← #1741
  1980 LoC  TNLean/MPS/Periodic/Overlap/             ← #1741
   234 LoC  TNLean/MPS/CanonicalForm/CyclicSectors/  ← #1765
   139 LoC  TNLean/MPS/CanonicalForm/                ← #1765
  5178 LoC  TNLean/MPS/CanonicalForm/SectorComparison/  ← #1742
   128 LoC  TNLean/MPS/Core/                         ← #1765
    62 LoC  TNLean/MPS/SharedInfra/                  ← #1765
    42 LoC  TNLean/Channel/Semigroup/                ← #1765
  -------
  9559 LoC total, 36 files
```

That is ≈8% of the 114,515 active-codebase LoC. All of it is on the
delete-or-retarget critical path for #1685; the resulting cleanup
will significantly reduce Lean's reload cost across the MPS layer.

### Active sorrys (excluding orphan tree and `Archive/`)

Each is gated by a tracked issue:

| File | sorries | LoC | Tracked by |
|---|---:|---:|---|
| `Channel/LorentzNormalForm.lean` | 3 | 345 | #1117 |
| `PEPS/FundamentalTheorem.lean` | 3 | 738 | #780 / #842 / #1252 stack |
| `MPS/ParentHamiltonian/UniqueGroundState.lean` | 2 | 939 | #1475 / #588 / #460 |
| `MPS/ParentHamiltonian/Martingale/Gap.lean` | 1 | 100 | #460 / #952 |

The four `Axioms/*.lean` files (`OperatorConvexity`, `Beigi`, `Entropy`)
carry axiom declarations by design (the project's named external-input
surface).

### Largest active files (>800 LoC)

```
997  MPS/FundamentalTheorem/PaperBNT/ProportionalMatch.lean   ← #1766
950  PEPS/Blocking.lean
943  Channel/Peripheral/CyclicDecomposition/CyclicProjections.lean
939  MPS/ParentHamiltonian/UniqueGroundState.lean
929  MPS/Core/BlockingInfrastructure.lean
916  Channel/Semigroup/RelaxationConditions.lean
907  MPS/ParentHamiltonian/WrappingWindow.lean
892  PiAlgebra/CanonicalFormSepAux.lean
857  MPS/Periodic/Overlap/SelfOverlap.lean   ← orphan (#1741)
835  MPS/Symmetry/StringOrderAux.lean
819  MPS/ParentHamiltonian/Martingale/Transport.lean
```

Only one (`ProportionalMatch.lean`) is in the hot PaperBNT/ area; the rest
are stable and don't urgently need splitting.

### Largest blueprint chapters (>1500 LoC)

```
3689  blueprint/src/chapter/ch14_parent_hamiltonian.tex
2599  blueprint/src/chapter/ch04_channels.tex
1937  blueprint/src/chapter/ch12_semigroup.tex
1825  blueprint/src/chapter/ch07_wielandt.tex
1704  blueprint/src/chapter/ch13_algebraic_ft.tex
1669  blueprint/src/chapter/ch06_spectral.tex
```

`ch14_parent_hamiltonian.tex` has 13 sections and would split cleanly
(ground space / parent interaction / intersection property / commuting /
decorrelation / spectral gap / degenerate ground space). Not opened as an
issue here because chapter splits are bigger projects and may not be
desired preemptively.

## Extrapolations from history

### Issue-creation velocity is accelerating

Open issues by week of creation:

```
2026-W11:  8
2026-W12: 12
2026-W14:  3
2026-W15:  7
2026-W16: 26
2026-W17: 10
2026-W18: 41
2026-W19: 27
```

May weeks W18 / W19 are running at ~5–6× the March rate. Most of the
increase is in `claude[bot]`-authored follow-up tickets generated by
review automation (32% of all currently-open issues are `claude[bot]`
follow-ups). The implication: every substantial feature PR is creating
2–3 downstream issues on average; without active cleanup the open-issue
count will continue to grow even as `main` advances.

### Predictable upcoming issues

From the observed pattern (every PaperBNT/ feature PR ships with a
blueprint-sync follow-up and a cleanup follow-up), the following are very
likely to be created in the next few weeks:

1. **Blueprint sync for #1756** when the final `IsCanonicalFormBNT`
   deletion lands — the four paper-gap notes in #1739 plus residual
   `\lean{IsCanonicalFormBNT.*}` tags in `ch08_canonical.tex` /
   `ch10_bnt.tex`.
2. **Phase 7 audit memo retirement**: a follow-up to fold the legacy
   `audits/2026-04-21_issue608_*.md`, `audits/2026-04-22_issue609_*.md`,
   etc. into a single Phase-7-closure record once the deletion waves stop.
3. **Split issues for `PaperBNT/Fundamental.lean` and
   `PaperBNT/StrongMatch.lean`** as they cross 800 LoC (both currently
   around 700–750 LoC and growing on each Phase E/F PR).
4. **Wave-5 cleanup**: stale `\uses{}` edges in `ch10_bnt.tex` after the
   Phase E global-gauge entries land — analogous to #1663 in ch11.
5. **PaperBNT.Examples expansion** — counter-examples for the new
   surface, mirroring the existing `Archive/BlockSepCounterexample.lean`
   pattern.

### Predictable bottleneck

The five paper-gap notes named in #1739 are still on disk and will keep
showing up in audits until they're rewritten or deleted. That issue has
the highest "bot will keep reopening this concern" risk.

## Numbers

- Before: 134 open
- Closed: 9 (3 completed + 6 superseded)
- Opened: 3 (#1756, #1765, #1766)
- After: 128 open

## Reproduction

The transitive-reachability orphan scan, the largest-file scan, and the
issue-creation-rate analysis are all single Python / shell snippets;
re-running them periodically is a one-liner in
`audits/2026-05-17_open_issues_audit.md` and an explicit code block in
the #1765 issue body.
