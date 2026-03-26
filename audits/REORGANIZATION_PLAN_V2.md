# TNLean Code Reorganization Plan — v2 (revised)

**Date**: 2026-03-13  
**Scope**: Full directory restructuring to Mathlib-standard naming and hierarchy  
**Current state**: 132 files, 40,701 lines, 10 flat directories, 0 subfolders  
**Revision note**: v2 incorporates findings from two independent validation passes:
a dependency-graph audit and a naming/conventions audit. All issues flagged have
been addressed.

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Diagnosis](#2-diagnosis)
3. [Guiding Principles](#3-guiding-principles)
4. [Proposed Directory Tree (revised)](#4-proposed-directory-tree-revised)
5. [Paper-Numbered File Renames](#5-paper-numbered-file-renames)
6. [Per-Module Reorganization](#6-per-module-reorganization)
7. [Legacy / Archive Pass](#7-legacy--archive-pass)
8. [Large File Splits](#8-large-file-splits)
9. [Compatibility Shim Strategy](#9-compatibility-shim-strategy)
10. [Migration Sequence](#10-migration-sequence)
11. [Validation Results & Fixes Applied](#11-validation-results--fixes-applied)

---

## 1. Executive Summary

The TNLean codebase has grown to 132 files but still uses the flat layout from
its early days. Three modules (MPS at 37 files, Wielandt at 34, Channel at 26)
are well past the threshold where Mathlib would introduce subfolders. Eleven
files use opaque paper-numbering (`Theorem1`, `Prop3_ac`, `Lemma2bExact`, etc.)
that is meaningless without knowing the paper. Several archival/legacy files sit
alongside active code with no visual distinction.

This plan proposes:
- **Subfolder splits** for the three large modules
- **Descriptive renames** for all paper-numbered files
- **An `Archive/` directory** for legacy compatibility wrappers
- **Compatibility shims** at old import paths during transition
- A **phased migration** that can be done incrementally

### Key design decision: topical vs layered

Validation revealed that the MPS and Wielandt dependency graphs contain
**bidirectional cycles between logical groups** (e.g., BNT ↔ FundamentalTheorem,
RankOne ↔ RectangularSpan). This means subfolders **cannot** be strictly layered
(where A/ never imports B/ if B/ imports A/). We therefore adopt **topical
grouping**: subfolders group files by mathematical topic for navigability, not as
a strict dependency DAG. This is documented explicitly so future contributors
don't mistakenly assume a layering contract.

---

## 2. Diagnosis

*(Unchanged from v1 — see `docs/REORGANIZATION_PLAN.md` §2 for full tables.)*

Key numbers:
- **Channel**: 26 files → needs subfolders
- **MPS**: 37 files → needs subfolders  
- **Wielandt**: 34 files → needs subfolders
- **11 files** with paper-numbered names
- **4 files** explicitly legacy/archival
- **18 files** over 500 lines (6 over 1000)

---

## 3. Guiding Principles

1. **Descriptive names**: File name tells you the mathematical content.
2. **Topical hierarchy**: Subfolders group by topic when directory exceeds ~12 files.
   Cross-subfolder imports within the same parent are expected and acceptable.
3. **`Defs.lean`** only for true definition-only files with no heavy imports.
   **`Basic.lean`** for foundational lemma files.
4. **No paper numbering** in filenames. Reference papers in module docstrings.
5. **No cryptic abbreviations** in filenames (CFII, NT, LI → expand or describe).
6. **No single-file subfolders** — fold into nearest topical neighbor.
7. **Target 200–500 lines** per file. Split anything >1000 where natural.
8. **Import stability**: Old imports continue via shim files during transition.
9. **`Archive/`** for explicitly retired/legacy/documentary code.

---

## 4. Proposed Directory Tree (revised)

Changes from v1 are marked with `← FIX`.

```
TNLean/
├── Algebra/                          # (13 files, unchanged)
│   ├── BlockPermutation.lean
│   ├── BlockTriangularTrace.lean
│   ├── BurnsideMatrix.lean
│   ├── BurnsideTheorem.lean
│   ├── GramMatrixLI.lean
│   ├── HermitianHelpers.lean
│   ├── IrreducibleTensorAction.lean
│   ├── MatrixFrobenius.lean
│   ├── NewtonGirard.lean
│   ├── ProjectionTriangularTrace.lean
│   ├── ScalarPowerSumIdentity.lean
│   ├── SkolemNoether.lean
│   └── TracePairing.lean
│
├── Archive/                          # NEW — retired/documentary code
│   ├── README.md                     # explains CFII abbreviation, archival status
│   ├── BlockSepCounterexample.lean   # was Scratch/
│   ├── BlockingPeriodicity.lean      # was MPS/ (legacy)
│   ├── BlockingPeriodicityCFII2.lean # was MPS/ (archival)
│   └── PeripheralClosure.lean        # was Channel/ (legacy)
│
├── Axioms/
│   └── BrouwerFixedPoint.lean        # rename from BrouwerFixedPointDensityMatrices
│
├── Channel/                          # (26 → 22 active, with subfolders)
│   ├── Basic.lean                    # was PositiveMap.lean
│   ├── DensityRetract.lean
│   ├── Primitive.lean
│   ├── WolfChapter6Index.lean        # documentation-only index
│   │
│   ├── FixedPoint/                   # (2 files — Ergodicity moved out)  ← FIX
│   │   ├── Cesaro.lean               # was CesaroFixedPoint
│   │   └── DSGauge.lean
│   │
│   ├── Irreducible/                  # (7 files — Ergodicity moved in)   ← FIX
│   │   ├── Basic.lean                # was Irreducible.lean
│   │   ├── Ergodicity.lean           # ← MOVED from FixedPoint (depends on IrreduciblePF)
│   │   ├── FromSpectral.lean         # was IrreducibleFromSpectral
│   │   ├── Growth.lean               # was IrreducibleGrowth
│   │   ├── PerronFrobenius.lean      # was IrreduciblePerronFrobenius
│   │   ├── Similarity.lean           # was SimilarityIrreducible
│   │   └── SpectralRadius.lean       # was IrreducibleSpectralRadius
│   │
│   ├── Peripheral/                   # (6 files)
│   │   ├── Spectrum.lean             # was PeripheralSpectrum
│   │   ├── ClosureFixedPoint.lean    # was PeripheralClosureFixedPoint
│   │   ├── Conjugation.lean          # was ConjugationSpectrum
│   │   ├── CyclicDecomposition.lean
│   │   ├── PeriodicityRemoval.lean
│   │   └── Powers.lean               # was PeripheralPowers
│   │
│   ├── PerronFrobenius/              # (2 files)
│   │   ├── Existence.lean            # was PerronFrobeniusExistence
│   │   └── Normalization.lean        # was PerronFrobeniusNormalization
│   │
│   └── Schwarz/                      # (4 files)
│       ├── Basic.lean                # was Schwarz.lean
│       ├── KadisonSchwarz.lean
│       ├── MultiplicativeDomain.lean
│       └── MultiplicativeDomainPowers.lean
│
├── MPS/                              # (37 → 32 active, with subfolders)
│   ├── Defs.lean                     # stays top-level (true base, no TNLean imports)
│   │
│   ├── Core/                         # ← RENAMED from Basic/ (not all foundational)
│   │   ├── Blocking.lean
│   │   ├── BlockingTransfer.lean
│   │   ├── CPPrimitive.lean
│   │   ├── MultiBlock.lean
│   │   ├── TPGauge.lean              # was TPGaugeFromAdjointFixedPoint
│   │   └── Transfer.lean
│   │                                 # CastLemmas REMOVED (→ Overlap/)     ← FIX
│   │                                 # TransferNormalization REMOVED (→ FT/) ← FIX
│   │
│   ├── BNT/                          # (5 files)
│   │   ├── Basic.lean                # was BNT.lean
│   │   ├── BasisNormal.lean
│   │   ├── Construction.lean         # was BNTConstruction
│   │   ├── PermutationRigidity.lean  # was BNTPermutationThm44
│   │   └── PermutationRigidityPrimitive.lean  # was BNTPermutationSimple ← FIX
│   │
│   ├── CanonicalForm/                # (6 files — gained BlockingViaAdjoint) ← FIX
│   │   ├── BlockingViaAdjoint.lean   # was BlockingPeriodicityCFII_viaAdjoint ← FIX
│   │   ├── Existence.lean            # was CanonicalFormExistence1606
│   │   ├── FromPeripheralPrimitive.lean
│   │   ├── FromPrimitive.lean
│   │   ├── NormalPipeline.lean       # was NormalCanonicalFormPipeline
│   │   └── Reduction.lean            # was CanonicalFormReduction
│   │
│   ├── FundamentalTheorem/           # (6 files — gained TransferNormalization) ← FIX
│   │   ├── Basic.lean                # was FundamentalTheorem.lean
│   │   ├── CoefficientConvergence.lean
│   │   ├── Full.lean                 # was FundamentalTheoremFull
│   │   ├── Multi.lean                # was FundamentalTheoremMulti
│   │   ├── Proportional.lean         # was FundamentalTheoremProportional
│   │   └── TransferNormalization.lean # ← MOVED from Core/ (imports FT/Multi)
│   │
│   ├── Irreducible/                  # (3 files)
│   │   ├── Adjoint.lean              # was IrreducibleAdjoint
│   │   ├── FormII.lean               # was IrreducibleFormII
│   │   └── FixedPointProjection.lean # was FixedPointInvariantProjection
│   │
│   ├── Overlap/                      # (4 files — gained CastLemmas)  ← FIX
│   │   ├── Basic.lean                # was MPVOverlap
│   │   ├── CastDecay.lean            # was CastOverlapDecay
│   │   ├── CastLemmas.lean           # ← MOVED from Core/ (imports MPVOverlap + CF/Reduction)
│   │   └── PeripheralToSpectralGap.lean
│   │
│   └── Structure/                    # (4 files)
│       ├── BlockPermutation.lean     # was BlockPermutationMPS
│       ├── InvariantSubspaceDecomp.lean
│       ├── LinearExtension.lean
│       └── PrimitivityBridge.lean
│
│   # NOTE: MPS/Periodicity/ ELIMINATED — single-file anti-pattern  ← FIX
│
├── PiAlgebra/                        # (4 files, unchanged)
│   ├── BlockSeparation.lean
│   ├── CanonicalFormSep.lean
│   ├── Construction.lean
│   └── FundamentalTheoremComplete.lean
│
├── QPF/                              # (3 files, unchanged)
│   ├── Assembly.lean
│   ├── PosDef.lean
│   └── Uniqueness.lean
│
├── Spectral/                         # (9 files, unchanged)
│   ├── CrossCorrelation.lean
│   ├── MixedTransfer.lean
│   ├── MPVOverlapDecay.lean
│   ├── MPVOverlapTrace.lean
│   ├── PrimitiveOverlap.lean
│   ├── SpectralGap.lean
│   ├── SpectralGapNT.lean           # NT = Normal Tensor; expand if Spectral/ ever reorganized
│   ├── SpectralGapRect.lean
│   └── TraceExpansion.lean
│
├── Topology/                         # (4 files, unchanged)
│   ├── BrouwerProduct.lean
│   ├── CompactRetractFixedPoint.lean
│   ├── ConvexProjection.lean
│   └── TendstoHelpers.lean
│
└── Wielandt/                         # (34 → 34 active, with subfolders)
    │
    ├── FittingDecomposition.lean     # standalone algebraic (top-level)
    ├── QuantumWielandt.lean          # top-level assembly
    ├── WielandtBound.lean            # ← PROMOTED to top-level (main theorem assembly) ← FIX
    │
    ├── Primitivity/                  # (8 files)
    │   ├── PaperDefinitions.lean     # was PrimitivePaper ← FIX (not "Defs" — has imports)
    │   ├── EasyDirections.lean       # was PrimitiveEquiv
    │   ├── Equivalence.lean          # was Prop3
    │   ├── ImpliesIrreducible.lean   # was PrimitiveImpliesIrreducible
    │   ├── ImpliesStronglyIrreducible.lean  # was Prop3_ac
    │   ├── Normal.lean               # was PrimitivityNormal
    │   ├── StronglyIrreducibleToFullRank.lean  # was Prop3_cb
    │   └── ToNormal.lean             # was PrimitivityToNormal
    │
    ├── SpanGrowth/                   # (6 files — Lemma2b moved in, WielandtBound moved out)
    │   ├── CumulativeSpan.lean
    │   ├── CumulativeToWordSpan.lean # ← KEPT original name (not "CumulativeToExact") ← FIX
    │   ├── EigenvectorSpreading.lean
    │   ├── InvertibleWordSpan.lean   # was InvertibleWordSpanGrowth
    │   ├── NonzeroTraceProduct.lean
    │   └── VectorToMatrixSpan.lean   # ← was Lemma2b, MOVED here (backend, not PaperResults) ← FIX
    │
    ├── RankOne/                      # (8 files)
    │   ├── BoundedWord.lean
    │   ├── Construction.lean
    │   ├── Element.lean
    │   ├── Extraction.lean
    │   ├── ExtractionFull.lean
    │   ├── Manufacture.lean
    │   ├── Products.lean
    │   └── SpanGrowth.lean
    │
    ├── RectangularSpan/              # (4 files)
    │   ├── Basic.lean                # was RectangularSpan
    │   ├── Growth.lean               # was RectSpanGrowth
    │   ├── Ranges.lean               # was RectangularRanges
    │   └── Universality.lean         # was RectSpanUniversality (1892 lines — split candidate)
    │
    └── PaperResults/                 # (5 files — Lemma2b removed, suffix fixes) ← FIX
        ├── WielandtInequality.lean   # was Theorem1
        ├── NonzeroTraceWord.lean     # was Lemma1
        ├── EigenvectorSpreading.lean # was Lemma2 ← FIX (dropped redundant "Paper" suffix)
        ├── MatrixSpanExistence.lean  # was Lemma2bCoarse
        └── MatrixSpanSharpBound.lean # was Lemma2bExact
```

---

## 5. Paper-Numbered File Renames

### Critical renames

| Old Path | New Path | Rationale |
|----------|----------|-----------|
| `Wielandt/Theorem1` | `Wielandt/PaperResults/WielandtInequality` | Main theorem gets its mathematical name |
| `Wielandt/Prop3` | `Wielandt/Primitivity/Equivalence` | "Proposition 3" = primitivity 3-way equivalence |
| `Wielandt/Prop3_ac` | `Wielandt/Primitivity/ImpliesStronglyIrreducible` | Direction (a)→(c) |
| `Wielandt/Prop3_cb` | `Wielandt/Primitivity/StronglyIrreducibleToFullRank` | Direction (c)→(b) |
| `Wielandt/Lemma1` | `Wielandt/PaperResults/NonzeroTraceWord` | Lemma 1 = nonzero trace word |
| `Wielandt/Lemma2` | `Wielandt/PaperResults/EigenvectorSpreading` | Lemma 2(a) (dropped "Paper" suffix) |
| `Wielandt/Lemma2b` | `Wielandt/SpanGrowth/VectorToMatrixSpan` | **Backend** file — not paper-facing |
| `Wielandt/Lemma2bCoarse` | `Wielandt/PaperResults/MatrixSpanExistence` | Coarse wrapper |
| `Wielandt/Lemma2bExact` | `Wielandt/PaperResults/MatrixSpanSharpBound` | Sharp D²−D+1 bound |

### Secondary renames

| Old Path | New Path | Rationale |
|----------|----------|-----------|
| `MPS/BNTPermutationThm44` | `MPS/BNT/PermutationRigidity` | Drop "Thm44" |
| `MPS/BNTPermutationSimple` | `MPS/BNT/PermutationRigidityPrimitive` | "Simple" → "Primitive" branch |
| `MPS/CanonicalFormExistence1606` | `MPS/CanonicalForm/Existence` | Drop arXiv number |
| `MPS/BlockingPeriodicityCFII_viaAdjoint` | `MPS/CanonicalForm/BlockingViaAdjoint` | Drop CFII, fold into CF/ |
| `Channel/PositiveMap` | `Channel/Basic` | Foundational definitions file |
| `Axioms/BrouwerFixedPointDensityMatrices` | `Axioms/BrouwerFixedPoint` | Shorter |
| `MPS/TPGaugeFromAdjointFixedPoint` | `MPS/Core/TPGauge` | Shorter |
| `Wielandt/PrimitivePaper` | `Wielandt/Primitivity/PaperDefinitions` | Not "Defs" (has heavy imports) |

---

## 6. Per-Module Reorganization

### 6.1 Channel (26 files → 5 subfolders + 4 top-level)

Key changes from v1:
- **`Ergodicity` moved to `Irreducible/`** (it imports `IrreduciblePerronFrobenius`;
  placing it in `FixedPoint/` would create a FixedPoint↔Irreducible cycle)
- `FixedPoint/` now has 2 files (Cesaro, DSGauge) — still above the single-file threshold

### 6.2 MPS (37 files → 6 subfolders + 1 top-level)

Key changes from v1:
- **Renamed `Basic/` → `Core/`** to avoid implying these are all foundational
- **`CastLemmas` moved to `Overlap/`** (imports MPVOverlap + CanonicalFormReduction)
- **`TransferNormalization` moved to `FundamentalTheorem/`** (imports FT/Multi)
- **`Periodicity/` eliminated** — was a single-file anti-pattern; its one active file
  (`BlockingPeriodicityCFII_viaAdjoint`) moved to `CanonicalForm/BlockingViaAdjoint`
- **`BNTPermutationSimple` renamed** to `PermutationRigidityPrimitive`

Note on sibling cycles: MPS has inherent bidirectional dependencies
(BNT ↔ FundamentalTheorem, CanonicalForm ↔ Irreducible, etc.). Subfolders
are topical groupings, not a strict layered DAG.

### 6.3 Wielandt (34 files → 4 subfolders + 3 top-level)

Key changes from v1:
- **`WielandtBound` promoted to top-level** (it's the main theorem assembly, not infrastructure)
- **`Lemma2b` moved to `SpanGrowth/VectorToMatrixSpan`** (it's a backend file imported by
  5 other backend modules — placing it in `PaperResults/` was backwards)
- **`PrimitivePaper` renamed to `Primitivity/PaperDefinitions`** (not `Defs` — it imports
  `WielandtBound`, `Transfer`, `PeripheralSpectrum`)
- **`CumulativeToWordSpan` keeps its original name** (not `CumulativeToExact` — "exact"
  is ambiguous in a math context)
- **`PaperResults/EigenvectorSpreading`** dropped redundant "Paper" suffix
- `PaperResults/` now contains only **5 true paper-facing wrappers** that are
  terminal nodes (not imported by backend code)

---

## 7. Legacy / Archive Pass

*(Unchanged from v1)*

Move 4 files to `TNLean/Archive/`:

| Source | Notes |
|--------|-------|
| `Channel/PeripheralClosure` | "Legacy wrapper" |
| `MPS/BlockingPeriodicity` | "Legacy wrapper" |
| `MPS/BlockingPeriodicityCFII2` | "archival alternate route" |
| `Scratch/BlockSepCounterexample` | Documentary counterexample |

`Archive/README.md` should explain:
- CFII = "Canonical Form II" / IrreducibleFormII gauge (from arXiv:1606.00608)
- These files are retained for reference but not part of the active library
- They are excluded from the root `TNLean.lean` import list

---

## 8. Large File Splits

*(Unchanged from v1 — see original plan for details)*

Priority split candidates:
- `Wielandt/RectSpanUniversality` (1,892 lines)
- `PiAlgebra/CanonicalFormSep` (1,598 lines)
- `Channel/CyclicDecomposition` (1,339 lines)
- `Wielandt/Prop3_ac` → `Primitivity/ImpliesStronglyIrreducible` (1,332 lines)

---

## 9. Compatibility Shim Strategy

*(Unchanged from v1)*

For each renamed file, leave a shim at the old path that re-exports the new location.
Shims are excluded from `TNLean.lean` and removed after one release cycle.

---

## 10. Migration Sequence

### Phase 0: Preparation
- [x] Create `docs/REORGANIZATION_PLAN.md` (v1)
- [x] Run dependency-graph validation
- [x] Run naming/conventions audit
- [x] Create `docs/REORGANIZATION_PLAN_V2.md` (this file)
- [ ] Review v2 with team
- [ ] `lake build` baseline

### Phase 1: Archive pass (low risk)
- [ ] Create `TNLean/Archive/` with README.md
- [ ] Move 4 legacy/archival files
- [ ] Create shims at old locations
- [ ] Remove `TNLean/Scratch/` directory
- [ ] `lake build`

### Phase 2: Channel subfolders
- [ ] Create `Channel/{Schwarz,Irreducible,Peripheral,PerronFrobenius,FixedPoint}/`
- [ ] Move files (including Ergodicity → Irreducible/)
- [ ] Update internal imports, create shims
- [ ] `lake build`

### Phase 3: MPS subfolders
- [ ] Create `MPS/{Core,BNT,CanonicalForm,FundamentalTheorem,Irreducible,Overlap,Structure}/`
- [ ] Move files with fixes (CastLemmas → Overlap/, TransferNormalization → FT/,
      CFII_viaAdjoint → CanonicalForm/BlockingViaAdjoint)
- [ ] Rename BNTPermutationThm44, CanonicalFormExistence1606, BNTPermutationSimple
- [ ] Create shims, update root imports
- [ ] `lake build`

### Phase 4: Wielandt subfolders + paper renames (highest impact)
- [ ] Create `Wielandt/{Primitivity,SpanGrowth,RankOne,RectangularSpan,PaperResults}/`
- [ ] Move files with fixes (Lemma2b → SpanGrowth/, WielandtBound stays top-level,
      PrimitivePaper → Primitivity/PaperDefinitions)
- [ ] Rename all paper-numbered files
- [ ] Create shims at all old locations
- [ ] `lake build`

### Phase 5: Large file splits (optional, can defer)
- [ ] Split `RectSpanUniversality` (1892 lines)
- [ ] Split `CanonicalFormSep` (1598 lines)
- [ ] `lake build`

### Phase 6: Cleanup
- [ ] Remove all shim files
- [ ] Final `lake build`
- [x] Update blueprint references — reviewed 2026-03-13; no module-path refs exist in blueprint sources (blueprint uses declaration names only); fixed 1 duplicate entry in `lean_decls` (`MPSTensor.toTensorFromBlocks`)

---

## 11. Validation Results & Fixes Applied

This section documents issues found by the two independent validation passes
and how each was resolved.

### Dependency-graph audit findings

| Issue | Original plan | Fix applied |
|-------|--------------|-------------|
| Ergodicity in FixedPoint/ creates FixedPoint↔Irreducible cycle | `Channel/FixedPoint/Ergodicity` | → `Channel/Irreducible/Ergodicity` |
| CastLemmas in Basic/ depends on CanonicalForm/ + Overlap/ | `MPS/Basic/CastLemmas` | → `MPS/Overlap/CastLemmas` |
| TransferNormalization in Basic/ depends on FundamentalTheorem/ | `MPS/Basic/TransferNormalization` | → `MPS/FundamentalTheorem/TransferNormalization` |
| Lemma2b in PaperResults/ imported by 5 backend files | `Wielandt/PaperResults/VectorToMatrixSpan` | → `Wielandt/SpanGrowth/VectorToMatrixSpan` |
| PrimitivePaper as Defs imports WielandtBound | `Wielandt/Primitivity/Defs` | → `Wielandt/Primitivity/PaperDefinitions` |
| MPS sibling cycles (BNT↔FT, CF↔Irred, etc.) | Implicit assumption of layering | Explicit: "topical grouping, not DAG" |

### Naming/conventions audit findings

| Issue | Original plan | Fix applied |
|-------|--------------|-------------|
| MPS/Periodicity/ = single-file subfolder | `MPS/Periodicity/CFIIViaAdjoint` | → `MPS/CanonicalForm/BlockingViaAdjoint` |
| WielandtBound buried in SpanGrowth/ | `Wielandt/SpanGrowth/WielandtBound` | → `Wielandt/WielandtBound` (top-level) |
| CumulativeToExact: "exact" ambiguous | `SpanGrowth/CumulativeToExact` | → `SpanGrowth/CumulativeToWordSpan` (keep original) |
| CFII abbreviation retained | `Periodicity/CFIIViaAdjoint` | → `CanonicalForm/BlockingViaAdjoint` |
| PermutationSimple misleading | `BNT/PermutationSimple` | → `BNT/PermutationRigidityPrimitive` |
| Redundant "Paper" suffix | `PaperResults/EigenvectorSpreadingPaper` | → `PaperResults/EigenvectorSpreading` |
| SpectralGapNT unexplained | Left as-is | Added note: NT = Normal Tensor |
| GramMatrixLI unexplained | Left as-is | Future: GramMatrixLinearIndep |
| BNTPermutationSimple archive candidate | Not flagged | Decision: keep (in TNLean.lean) |

### Confirmed sound (no changes needed)

- `Channel/Basic.lean` (PositiveMap) as base: ✅ no TNLean imports
- `MPS/Defs.lean` stays top-level: ✅ no TNLean imports, 11 downstream importers
- Archive moves safe: ✅ no active imports of any archived file
- All 132 files accounted for: ✅ no path collisions

---

## Appendix: Full Old→New Path Mapping (revised)

<details>
<summary>Click to expand complete mapping</summary>

### Algebra (unchanged)
```
TNLean/Algebra/*.lean → (no change, all 13 files)
```

### Archive (new)
```
TNLean/Scratch/BlockSepCounterexample.lean   → TNLean/Archive/BlockSepCounterexample.lean
TNLean/Channel/PeripheralClosure.lean        → TNLean/Archive/PeripheralClosure.lean
TNLean/MPS/BlockingPeriodicity.lean          → TNLean/Archive/BlockingPeriodicity.lean
TNLean/MPS/BlockingPeriodicityCFII2.lean     → TNLean/Archive/BlockingPeriodicityCFII2.lean
```

### Axioms
```
TNLean/Axioms/BrouwerFixedPointDensityMatrices.lean → TNLean/Axioms/BrouwerFixedPoint.lean
```

### Channel
```
TNLean/Channel/PositiveMap.lean              → TNLean/Channel/Basic.lean
TNLean/Channel/DensityRetract.lean           → (no change)
TNLean/Channel/Primitive.lean                → (no change)
TNLean/Channel/WolfChapter6.lean             → TNLean/Channel/WolfChapter6Index.lean

TNLean/Channel/Schwarz.lean                  → TNLean/Channel/Schwarz/Basic.lean
TNLean/Channel/KadisonSchwarz.lean           → TNLean/Channel/Schwarz/KadisonSchwarz.lean
TNLean/Channel/MultiplicativeDomain.lean     → TNLean/Channel/Schwarz/MultiplicativeDomain.lean
TNLean/Channel/MultiplicativeDomainPowers.lean → TNLean/Channel/Schwarz/MultiplicativeDomainPowers.lean

TNLean/Channel/Irreducible.lean              → TNLean/Channel/Irreducible/Basic.lean
TNLean/Channel/Ergodicity.lean               → TNLean/Channel/Irreducible/Ergodicity.lean  ← FIX
TNLean/Channel/IrreducibleGrowth.lean        → TNLean/Channel/Irreducible/Growth.lean
TNLean/Channel/IrreduciblePerronFrobenius.lean → TNLean/Channel/Irreducible/PerronFrobenius.lean
TNLean/Channel/IrreducibleSpectralRadius.lean → TNLean/Channel/Irreducible/SpectralRadius.lean
TNLean/Channel/IrreducibleFromSpectral.lean  → TNLean/Channel/Irreducible/FromSpectral.lean
TNLean/Channel/SimilarityIrreducible.lean    → TNLean/Channel/Irreducible/Similarity.lean

TNLean/Channel/PeripheralSpectrum.lean       → TNLean/Channel/Peripheral/Spectrum.lean
TNLean/Channel/PeripheralPowers.lean         → TNLean/Channel/Peripheral/Powers.lean
TNLean/Channel/PeripheralClosureFixedPoint.lean → TNLean/Channel/Peripheral/ClosureFixedPoint.lean
TNLean/Channel/ConjugationSpectrum.lean      → TNLean/Channel/Peripheral/Conjugation.lean
TNLean/Channel/CyclicDecomposition.lean      → TNLean/Channel/Peripheral/CyclicDecomposition.lean
TNLean/Channel/PeriodicityRemoval.lean       → TNLean/Channel/Peripheral/PeriodicityRemoval.lean

TNLean/Channel/PerronFrobeniusExistence.lean → TNLean/Channel/PerronFrobenius/Existence.lean
TNLean/Channel/PerronFrobeniusNormalization.lean → TNLean/Channel/PerronFrobenius/Normalization.lean

TNLean/Channel/CesaroFixedPoint.lean         → TNLean/Channel/FixedPoint/Cesaro.lean
TNLean/Channel/DSGauge.lean                  → TNLean/Channel/FixedPoint/DSGauge.lean
```

### MPS
```
TNLean/MPS/Defs.lean                         → (no change, top-level)

TNLean/MPS/Transfer.lean                     → TNLean/MPS/Core/Transfer.lean
TNLean/MPS/Blocking.lean                     → TNLean/MPS/Core/Blocking.lean
TNLean/MPS/BlockingTransfer.lean             → TNLean/MPS/Core/BlockingTransfer.lean
TNLean/MPS/CPPrimitive.lean                  → TNLean/MPS/Core/CPPrimitive.lean
TNLean/MPS/MultiBlock.lean                   → TNLean/MPS/Core/MultiBlock.lean
TNLean/MPS/TPGaugeFromAdjointFixedPoint.lean → TNLean/MPS/Core/TPGauge.lean

TNLean/MPS/BNT.lean                          → TNLean/MPS/BNT/Basic.lean
TNLean/MPS/BasisNormal.lean                  → TNLean/MPS/BNT/BasisNormal.lean
TNLean/MPS/BNTConstruction.lean              → TNLean/MPS/BNT/Construction.lean
TNLean/MPS/BNTPermutationThm44.lean          → TNLean/MPS/BNT/PermutationRigidity.lean
TNLean/MPS/BNTPermutationSimple.lean         → TNLean/MPS/BNT/PermutationRigidityPrimitive.lean  ← FIX

TNLean/MPS/CanonicalFormReduction.lean       → TNLean/MPS/CanonicalForm/Reduction.lean
TNLean/MPS/CanonicalFormFromPrimitive.lean   → TNLean/MPS/CanonicalForm/FromPrimitive.lean
TNLean/MPS/CanonicalFormFromPeripheralPrimitive.lean → TNLean/MPS/CanonicalForm/FromPeripheralPrimitive.lean
TNLean/MPS/CanonicalFormExistence1606.lean   → TNLean/MPS/CanonicalForm/Existence.lean
TNLean/MPS/NormalCanonicalFormPipeline.lean  → TNLean/MPS/CanonicalForm/NormalPipeline.lean
TNLean/MPS/BlockingPeriodicityCFII_viaAdjoint.lean → TNLean/MPS/CanonicalForm/BlockingViaAdjoint.lean  ← FIX

TNLean/MPS/FundamentalTheorem.lean           → TNLean/MPS/FundamentalTheorem/Basic.lean
TNLean/MPS/FundamentalTheoremProportional.lean → TNLean/MPS/FundamentalTheorem/Proportional.lean
TNLean/MPS/FundamentalTheoremMulti.lean      → TNLean/MPS/FundamentalTheorem/Multi.lean
TNLean/MPS/FundamentalTheoremFull.lean       → TNLean/MPS/FundamentalTheorem/Full.lean
TNLean/MPS/CoefficientConvergence.lean       → TNLean/MPS/FundamentalTheorem/CoefficientConvergence.lean
TNLean/MPS/TransferNormalization.lean        → TNLean/MPS/FundamentalTheorem/TransferNormalization.lean  ← FIX

TNLean/MPS/IrreducibleFormII.lean            → TNLean/MPS/Irreducible/FormII.lean
TNLean/MPS/IrreducibleAdjoint.lean           → TNLean/MPS/Irreducible/Adjoint.lean
TNLean/MPS/FixedPointInvariantProjection.lean → TNLean/MPS/Irreducible/FixedPointProjection.lean

TNLean/MPS/MPVOverlap.lean                   → TNLean/MPS/Overlap/Basic.lean
TNLean/MPS/CastOverlapDecay.lean             → TNLean/MPS/Overlap/CastDecay.lean
TNLean/MPS/CastLemmas.lean                   → TNLean/MPS/Overlap/CastLemmas.lean  ← FIX
TNLean/MPS/PeripheralToSpectralGap.lean      → TNLean/MPS/Overlap/PeripheralToSpectralGap.lean

TNLean/MPS/BlockPermutationMPS.lean          → TNLean/MPS/Structure/BlockPermutation.lean
TNLean/MPS/InvariantSubspaceDecomp.lean      → TNLean/MPS/Structure/InvariantSubspaceDecomp.lean
TNLean/MPS/LinearExtension.lean              → TNLean/MPS/Structure/LinearExtension.lean
TNLean/MPS/PrimitivityBridge.lean            → TNLean/MPS/Structure/PrimitivityBridge.lean
```

### PiAlgebra, QPF, Spectral, Topology (unchanged)
```
(all files remain at current paths)
```

### Wielandt
```
TNLean/Wielandt/FittingDecomposition.lean     → (no change, top-level)
TNLean/Wielandt/QuantumWielandt.lean          → (no change, top-level)
TNLean/Wielandt/WielandtBound.lean            → (no change, top-level)  ← FIX (was SpanGrowth/)

TNLean/Wielandt/PrimitivePaper.lean           → TNLean/Wielandt/Primitivity/PaperDefinitions.lean  ← FIX
TNLean/Wielandt/PrimitiveEquiv.lean           → TNLean/Wielandt/Primitivity/EasyDirections.lean
TNLean/Wielandt/Prop3.lean                    → TNLean/Wielandt/Primitivity/Equivalence.lean
TNLean/Wielandt/Prop3_ac.lean                 → TNLean/Wielandt/Primitivity/ImpliesStronglyIrreducible.lean
TNLean/Wielandt/Prop3_cb.lean                 → TNLean/Wielandt/Primitivity/StronglyIrreducibleToFullRank.lean
TNLean/Wielandt/PrimitiveImpliesIrreducible.lean → TNLean/Wielandt/Primitivity/ImpliesIrreducible.lean
TNLean/Wielandt/PrimitivityNormal.lean        → TNLean/Wielandt/Primitivity/Normal.lean
TNLean/Wielandt/PrimitivityToNormal.lean      → TNLean/Wielandt/Primitivity/ToNormal.lean

TNLean/Wielandt/CumulativeSpan.lean           → TNLean/Wielandt/SpanGrowth/CumulativeSpan.lean
TNLean/Wielandt/CumulativeToWordSpan.lean     → TNLean/Wielandt/SpanGrowth/CumulativeToWordSpan.lean  ← FIX
TNLean/Wielandt/EigenvectorSpreading.lean     → TNLean/Wielandt/SpanGrowth/EigenvectorSpreading.lean
TNLean/Wielandt/InvertibleWordSpanGrowth.lean → TNLean/Wielandt/SpanGrowth/InvertibleWordSpan.lean
TNLean/Wielandt/NonzeroTraceProduct.lean      → TNLean/Wielandt/SpanGrowth/NonzeroTraceProduct.lean
TNLean/Wielandt/Lemma2b.lean                  → TNLean/Wielandt/SpanGrowth/VectorToMatrixSpan.lean  ← FIX

TNLean/Wielandt/RankOneConstruction.lean      → TNLean/Wielandt/RankOne/Construction.lean
TNLean/Wielandt/RankOneElement.lean           → TNLean/Wielandt/RankOne/Element.lean
TNLean/Wielandt/RankOneExtraction.lean        → TNLean/Wielandt/RankOne/Extraction.lean
TNLean/Wielandt/RankOneExtractionFull.lean    → TNLean/Wielandt/RankOne/ExtractionFull.lean
TNLean/Wielandt/RankOneManufacture.lean       → TNLean/Wielandt/RankOne/Manufacture.lean
TNLean/Wielandt/RankOneProducts.lean          → TNLean/Wielandt/RankOne/Products.lean
TNLean/Wielandt/RankOneSpanGrowth.lean        → TNLean/Wielandt/RankOne/SpanGrowth.lean
TNLean/Wielandt/RankOneBoundedWord.lean       → TNLean/Wielandt/RankOne/BoundedWord.lean

TNLean/Wielandt/RectangularRanges.lean        → TNLean/Wielandt/RectangularSpan/Ranges.lean
TNLean/Wielandt/RectangularSpan.lean          → TNLean/Wielandt/RectangularSpan/Basic.lean
TNLean/Wielandt/RectSpanGrowth.lean           → TNLean/Wielandt/RectangularSpan/Growth.lean
TNLean/Wielandt/RectSpanUniversality.lean     → TNLean/Wielandt/RectangularSpan/Universality.lean

TNLean/Wielandt/Theorem1.lean                 → TNLean/Wielandt/PaperResults/WielandtInequality.lean
TNLean/Wielandt/Lemma1.lean                   → TNLean/Wielandt/PaperResults/NonzeroTraceWord.lean
TNLean/Wielandt/Lemma2.lean                   → TNLean/Wielandt/PaperResults/EigenvectorSpreading.lean  ← FIX
TNLean/Wielandt/Lemma2bCoarse.lean            → TNLean/Wielandt/PaperResults/MatrixSpanExistence.lean
TNLean/Wielandt/Lemma2bExact.lean             → TNLean/Wielandt/PaperResults/MatrixSpanSharpBound.lean
```

</details>

---

*End of revised plan. Ready for execution.*
