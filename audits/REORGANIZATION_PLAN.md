# TNLean Code Reorganization Plan

> **⚠ SUPERSEDED**: This is the initial v1 plan. Two validation passes found issues (see §11 of the v2 plan). The executed plan is `docs/REORGANIZATION_PLAN_V2.md`. Key differences from v1: `Lemma2 → PaperResults/EigenvectorSpreading` (not `EigenvectorSpreadingPaper`), `Lemma2b → SpanGrowth/VectorToMatrixSpan` (not `PaperResults/VectorToMatrixSpan`). See v2 for the full corrected mapping.

**Date**: 2026-03-13  
**Scope**: Full directory restructuring to Mathlib-standard naming and hierarchy  
**Current state**: 132 files, 40,701 lines, 10 flat directories, 0 subfolders

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Diagnosis](#2-diagnosis)
3. [Guiding Principles](#3-guiding-principles)
4. [Proposed Directory Tree](#4-proposed-directory-tree)
5. [Paper-Numbered File Renames](#5-paper-numbered-file-renames)
6. [Per-Module Reorganization](#6-per-module-reorganization)
7. [Legacy / Archive Pass](#7-legacy--archive-pass)
8. [Large File Splits](#8-large-file-splits)
9. [Compatibility Shim Strategy](#9-compatibility-shim-strategy)
10. [Migration Sequence](#10-migration-sequence)

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

---

## 2. Diagnosis

### 2.1 Files per directory

| Directory | Files | Lines | Verdict |
|-----------|-------|-------|---------|
| `Algebra` | 13 | 2,109 | OK — at upper limit |
| `Axioms` | 1 | 54 | OK — might fold into Channel |
| `Channel` | 26 | 8,186 | **Needs subfolders** |
| `MPS` | 37 | 10,540 | **Needs subfolders** |
| `PiAlgebra` | 4 | 2,282 | OK |
| `QPF` | 3 | 800 | OK |
| `Scratch` | 1 | 187 | Move to Archive |
| `Spectral` | 9 | 4,054 | OK |
| `Topology` | 4 | 381 | OK |
| `Wielandt` | 34 | 12,108 | **Needs subfolders** |

### 2.2 Paper-numbered filenames (11 files)

| Current name | Paper reference | Actual content |
|-------------|-----------------|----------------|
| `Wielandt/Theorem1` | arXiv:0909.5347 Thm 1 | Quantum Wielandt inequality |
| `Wielandt/Prop3` | arXiv:0909.5347 Prop 3 | Primitivity equivalence (full) |
| `Wielandt/Prop3_ac` | Prop 3, (a)→(c) | Primitive → strongly irreducible |
| `Wielandt/Prop3_cb` | Prop 3, (c)→(b) | Strongly irred → full Kraus rank |
| `Wielandt/Lemma1` | arXiv:0909.5347 Lem 1 | Nonzero trace word existence |
| `Wielandt/Lemma2` | arXiv:0909.5347 Lem 2(a) | Eigenvector spreading wrapper |
| `Wielandt/Lemma2b` | arXiv:0909.5347 Lem 2(b) | Vector→matrix span assembly |
| `Wielandt/Lemma2bCoarse` | Lem 2(b), coarse | Matrix span ∃ bound |
| `Wielandt/Lemma2bExact` | Lem 2(b), exact | Matrix span D²−D+1 bound |
| `MPS/BNTPermutationThm44` | arXiv:2011.12127 Thm 4.4 | BNT permutation rigidity |
| `MPS/CanonicalFormExistence1606` | arXiv:1606.00608 | Canonical form existence pipeline |

### 2.3 Legacy / archival files (5 files)

| File | Status |
|------|--------|
| `Channel/PeripheralClosure` | Explicitly "Legacy wrapper" |
| `MPS/BlockingPeriodicity` | Explicitly "Legacy wrapper" |
| `MPS/BlockingPeriodicityCFII2` | Explicitly "archival" alternate route |
| `Scratch/BlockSepCounterexample` | Documentary counterexample |
| `Channel/WolfChapter6` | Documentation-only re-export index |

### 2.4 Oversized files (>800 lines, 18 files)

| File | Lines | Split candidate? |
|------|-------|-----------------|
| `Wielandt/RectSpanUniversality` | 1,892 | Yes — sharp backends + universality |
| `PiAlgebra/CanonicalFormSep` | 1,598 | Yes — separation + canonical form |
| `Channel/CyclicDecomposition` | 1,339 | Maybe — logically cohesive |
| `Wielandt/Prop3_ac` | 1,332 | Yes — multiple helper lemmas |
| `Spectral/SpectralGapNT` | 1,229 | Yes — NT-specific vs general |
| `Spectral/SpectralGap` | 1,175 | Maybe — core module |
| `Wielandt/Prop3_cb` | 929 | Borderline |
| `Channel/IrreducibleGrowth` | 925 | Borderline |
| `MPS/BNTPermutationThm44` | 923 | Yes after rename |
| `MPS/BlockingPeriodicityCFII2` | 922 | No — archival |
| `MPS/InvariantSubspaceDecomp` | 863 | Borderline |

---

## 3. Guiding Principles

Following Mathlib conventions:

1. **Descriptive names**: File name tells you the mathematical content.
   `PrimitivityEquivalence.lean` not `Prop3.lean`.
2. **Hierarchy**: When a directory exceeds ~12 files, introduce subfolders.
3. **`Defs.lean`** for foundational definitions, **`Basic.lean`** for core lemmas.
4. **No paper numbering** in filenames. Reference papers in module docstrings.
5. **Target 200–500 lines** per file. Tolerate up to ~800 for cohesive modules.
   Split anything >1000 lines where there's a natural seam.
6. **Import stability**: Old imports continue to work via shim files during transition.
7. **`Archive/`** for explicitly retired/legacy/documentary code.

---

## 4. Proposed Directory Tree

```
TNLean/
├── Algebra/                          # (13 files → 13 files, no change needed)
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
│   ├── BlockSepCounterexample.lean   # was Scratch/
│   ├── BlockingPeriodicity.lean      # was MPS/ (legacy)
│   ├── BlockingPeriodicityCFII2.lean # was MPS/ (archival)
│   └── PeripheralClosure.lean        # was Channel/ (legacy)
│
├── Axioms/                           # (1 file, keep for now)
│   └── BrouwerFixedPoint.lean        # rename from BrouwerFixedPointDensityMatrices
│
├── Channel/                          # (26 → 22 active files, with subfolders)
│   ├── Basic.lean                    # was PositiveMap.lean
│   ├── DensityRetract.lean
│   ├── Primitive.lean
│   ├── WolfChapter6Index.lean        # rename; documentation-only
│   │
│   ├── FixedPoint/                   # NEW subfolder
│   │   ├── Cesaro.lean               # was CesaroFixedPoint
│   │   ├── DSGauge.lean
│   │   └── Ergodicity.lean
│   │
│   ├── Irreducible/                  # NEW subfolder
│   │   ├── Basic.lean                # was Irreducible.lean
│   │   ├── FromSpectral.lean         # was IrreducibleFromSpectral
│   │   ├── Growth.lean               # was IrreducibleGrowth
│   │   ├── PerronFrobenius.lean      # was IrreduciblePerronFrobenius
│   │   ├── Similarity.lean           # was SimilarityIrreducible
│   │   └── SpectralRadius.lean       # was IrreducibleSpectralRadius
│   │
│   ├── Peripheral/                   # NEW subfolder
│   │   ├── Spectrum.lean             # was PeripheralSpectrum
│   │   ├── ClosureFixedPoint.lean    # was PeripheralClosureFixedPoint
│   │   ├── Conjugation.lean          # was ConjugationSpectrum
│   │   ├── CyclicDecomposition.lean  # was CyclicDecomposition
│   │   ├── PeriodicityRemoval.lean
│   │   └── Powers.lean               # was PeripheralPowers
│   │
│   ├── PerronFrobenius/              # NEW subfolder
│   │   ├── Existence.lean            # was PerronFrobeniusExistence
│   │   └── Normalization.lean        # was PerronFrobeniusNormalization
│   │
│   └── Schwarz/                      # NEW subfolder
│       ├── Basic.lean                # was Schwarz.lean
│       ├── KadisonSchwarz.lean
│       ├── MultiplicativeDomain.lean
│       └── MultiplicativeDomainPowers.lean
│
├── MPS/                              # (37 → 32 active files, with subfolders)
│   ├── Defs.lean                     # keep
│   │
│   ├── Basic/                        # NEW subfolder — core transfer/blocking
│   │   ├── Blocking.lean
│   │   ├── BlockingTransfer.lean
│   │   ├── CastLemmas.lean
│   │   ├── CPPrimitive.lean
│   │   ├── MultiBlock.lean
│   │   ├── Transfer.lean
│   │   ├── TransferNormalization.lean
│   │   └── TPGauge.lean              # was TPGaugeFromAdjointFixedPoint
│   │
│   ├── BNT/                          # NEW subfolder — basis-normal tensors
│   │   ├── Basic.lean                # was BNT.lean
│   │   ├── BasisNormal.lean
│   │   ├── Construction.lean         # was BNTConstruction
│   │   ├── PermutationRigidity.lean  # was BNTPermutationThm44 ← RENAME
│   │   └── PermutationSimple.lean    # was BNTPermutationSimple
│   │
│   ├── CanonicalForm/                # NEW subfolder
│   │   ├── Existence.lean            # was CanonicalFormExistence1606 ← RENAME
│   │   ├── FromPeripheralPrimitive.lean # was CanonicalFormFromPeripheralPrimitive
│   │   ├── FromPrimitive.lean        # was CanonicalFormFromPrimitive
│   │   ├── NormalPipeline.lean       # was NormalCanonicalFormPipeline
│   │   └── Reduction.lean            # was CanonicalFormReduction
│   │
│   ├── FundamentalTheorem/           # NEW subfolder
│   │   ├── Basic.lean                # was FundamentalTheorem.lean
│   │   ├── CoefficientConvergence.lean
│   │   ├── Full.lean                 # was FundamentalTheoremFull
│   │   ├── Multi.lean                # was FundamentalTheoremMulti
│   │   └── Proportional.lean         # was FundamentalTheoremProportional
│   │
│   ├── Irreducible/                  # NEW subfolder
│   │   ├── Adjoint.lean              # was IrreducibleAdjoint
│   │   ├── FormII.lean               # was IrreducibleFormII
│   │   └── FixedPointProjection.lean # was FixedPointInvariantProjection
│   │
│   ├── Overlap/                      # NEW subfolder
│   │   ├── Basic.lean                # was MPVOverlap
│   │   ├── CastDecay.lean            # was CastOverlapDecay
│   │   └── PeripheralToSpectralGap.lean
│   │
│   ├── Periodicity/                  # NEW subfolder
│   │   └── CFIIViaAdjoint.lean       # was BlockingPeriodicityCFII_viaAdjoint
│   │
│   └── Structure/                    # NEW subfolder
│       ├── BlockPermutation.lean     # was BlockPermutationMPS
│       ├── InvariantSubspaceDecomp.lean
│       ├── LinearExtension.lean
│       └── PrimitivityBridge.lean
│
├── PiAlgebra/                        # (4 files, keep flat)
│   ├── BlockSeparation.lean
│   ├── CanonicalFormSep.lean         # consider splitting (1598 lines)
│   ├── Construction.lean
│   └── FundamentalTheoremComplete.lean
│
├── QPF/                              # (3 files, keep flat)
│   ├── Assembly.lean
│   ├── PosDef.lean
│   └── Uniqueness.lean
│
├── Spectral/                         # (9 files, keep flat)
│   ├── CrossCorrelation.lean
│   ├── MixedTransfer.lean
│   ├── MPVOverlapDecay.lean
│   ├── MPVOverlapTrace.lean
│   ├── PrimitiveOverlap.lean
│   ├── SpectralGap.lean
│   ├── SpectralGapNT.lean
│   ├── SpectralGapRect.lean
│   └── TraceExpansion.lean
│
├── Topology/                         # (4 files, keep flat)
│   ├── BrouwerProduct.lean
│   ├── CompactRetractFixedPoint.lean
│   ├── ConvexProjection.lean
│   └── TendstoHelpers.lean
│
└── Wielandt/                         # (34 → 34 active files, with subfolders)
    │
    ├── Primitivity/                  # NEW subfolder — definitions & equivalences
    │   ├── Defs.lean                 # was PrimitivePaper
    │   ├── EasyDirections.lean       # was PrimitiveEquiv
    │   ├── Equivalence.lean          # was Prop3 ← KEY RENAME
    │   ├── ImpliesIrreducible.lean   # was PrimitiveImpliesIrreducible
    │   ├── ImpliesStronglyIrreducible.lean  # was Prop3_ac ← KEY RENAME
    │   ├── Normal.lean               # was PrimitivityNormal
    │   ├── StronglyIrreducibleToFullRank.lean  # was Prop3_cb ← KEY RENAME
    │   └── ToNormal.lean             # was PrimitivityToNormal
    │
    ├── SpanGrowth/                   # NEW subfolder — span infrastructure
    │   ├── CumulativeSpan.lean
    │   ├── CumulativeToExact.lean    # was CumulativeToWordSpan
    │   ├── EigenvectorSpreading.lean
    │   ├── InvertibleWordSpan.lean   # was InvertibleWordSpanGrowth
    │   ├── NonzeroTraceProduct.lean
    │   └── WielandtBound.lean
    │
    ├── RankOne/                      # NEW subfolder — rank-one machinery
    │   ├── BoundedWord.lean          # was RankOneBoundedWord
    │   ├── Construction.lean         # was RankOneConstruction
    │   ├── Element.lean              # was RankOneElement
    │   ├── Extraction.lean           # was RankOneExtraction
    │   ├── ExtractionFull.lean       # was RankOneExtractionFull
    │   ├── Manufacture.lean          # was RankOneManufacture
    │   ├── Products.lean             # was RankOneProducts
    │   └── SpanGrowth.lean           # was RankOneSpanGrowth
    │
    ├── RectangularSpan/              # NEW subfolder
    │   ├── Basic.lean                # was RectangularSpan
    │   ├── Growth.lean               # was RectSpanGrowth
    │   ├── Ranges.lean               # was RectangularRanges
    │   └── Universality.lean         # was RectSpanUniversality (1892 lines!)
    │
    ├── FittingDecomposition.lean     # standalone, algebraic
    │
    ├── PaperResults/                 # NEW subfolder — paper-facing wrappers
    │   ├── NonzeroTraceWord.lean     # was Lemma1 ← KEY RENAME
    │   ├── EigenvectorSpreadingPaper.lean  # was Lemma2 ← KEY RENAME
    │   ├── VectorToMatrixSpan.lean   # was Lemma2b ← KEY RENAME
    │   ├── MatrixSpanExistence.lean  # was Lemma2bCoarse ← KEY RENAME
    │   ├── MatrixSpanSharpBound.lean # was Lemma2bExact ← KEY RENAME
    │   └── WielandtInequality.lean   # was Theorem1 ← KEY RENAME
    │
    └── QuantumWielandt.lean          # top-level assembly (keep)
```

---

## 5. Paper-Numbered File Renames

### Critical renames (Wielandt paper-facing wrappers)

| Old Path | New Path | Rationale |
|----------|----------|-----------|
| `Wielandt/Theorem1` | `Wielandt/PaperResults/WielandtInequality` | The _main theorem_ deserves its mathematical name |
| `Wielandt/Prop3` | `Wielandt/Primitivity/Equivalence` | "Proposition 3" = primitivity 3-way equivalence |
| `Wielandt/Prop3_ac` | `Wielandt/Primitivity/ImpliesStronglyIrreducible` | Direction (a)→(c) of Prop 3 |
| `Wielandt/Prop3_cb` | `Wielandt/Primitivity/StronglyIrreducibleToFullRank` | Direction (c)→(b) of Prop 3 |
| `Wielandt/Lemma1` | `Wielandt/PaperResults/NonzeroTraceWord` | Lemma 1 = nonzero trace word |
| `Wielandt/Lemma2` | `Wielandt/PaperResults/EigenvectorSpreadingPaper` | Lemma 2(a) = eigenvector spreading |
| `Wielandt/Lemma2b` | `Wielandt/PaperResults/VectorToMatrixSpan` | Lemma 2(b) core = vector→matrix |
| `Wielandt/Lemma2bCoarse` | `Wielandt/PaperResults/MatrixSpanExistence` | Lemma 2(b) coarse |
| `Wielandt/Lemma2bExact` | `Wielandt/PaperResults/MatrixSpanSharpBound` | Lemma 2(b) exact D²−D+1 |

### Secondary renames

| Old Path | New Path | Rationale |
|----------|----------|-----------|
| `MPS/BNTPermutationThm44` | `MPS/BNT/PermutationRigidity` | Drop "Thm44", describe content |
| `MPS/CanonicalFormExistence1606` | `MPS/CanonicalForm/Existence` | Drop arXiv number |
| `Axioms/BrouwerFixedPointDensityMatrices` | `Axioms/BrouwerFixedPoint` | Shorter, clear |
| `Channel/PositiveMap` | `Channel/Basic` | This is the base definitions file |
| `MPS/TPGaugeFromAdjointFixedPoint` | `MPS/Basic/TPGauge` | Shorter name |

---

## 6. Per-Module Reorganization

### 6.1 Channel (26 files → 5 subfolders + 4 top-level)

**Rationale**: The Channel module covers quantum channel theory organized around
several natural topics: Schwarz/multiplicative domain, irreducibility theory,
peripheral spectrum, Perron-Frobenius, and fixed points.

**Subfolders**:
- `Schwarz/` (4 files): Schwarz inequality, Kadison-Schwarz, multiplicative domain
- `Irreducible/` (6 files): Irreducible CP maps and their spectral properties
- `Peripheral/` (6 files): Peripheral spectrum, cyclic decomposition, periodicity
- `PerronFrobenius/` (2 files): PF existence and normalization
- `FixedPoint/` (3 files): Cesàro fixed points, ergodicity, DS gauge

**Top-level files** (stay at `Channel/`):
- `Basic.lean` (was PositiveMap): foundational definitions
- `DensityRetract.lean`: preparatory maps
- `Primitive.lean`: primitive channels (small, cross-cutting)
- `WolfChapter6Index.lean`: documentation-only index

### 6.2 MPS (37 files → 7 subfolders + 1 top-level)

**Rationale**: The MPS module is the largest and covers the full fundamental
theorem pipeline. Natural groups: basic infrastructure, BNT construction,
canonical form, fundamental theorem variants, irreducible form analysis.

**Subfolders**:
- `Basic/` (8 files): Core definitions, transfer, blocking, multiblock
- `BNT/` (5 files): Basis normal tensors and permutation rigidity
- `CanonicalForm/` (5 files): Canonical form existence and reduction
- `FundamentalTheorem/` (5 files): All FT variants and coefficient convergence
- `Irreducible/` (3 files): Irreducible form II, adjoint, fixed-point projection
- `Overlap/` (3 files): MPV overlaps and peripheral→spectral gap bridge
- `Structure/` (4 files): Block permutation, invariant subspaces, linear extension

### 6.3 Wielandt (34 files → 4 subfolders + 2 top-level)

**Rationale**: The Wielandt module has the most naming problems. It mixes
backend span-growth machinery, rank-one construction pipeline, rectangular span
theory, primitivity equivalences, and paper-facing wrappers all in one flat
directory.

**Subfolders**:
- `Primitivity/` (8 files): All primitivity definitions and equivalences
- `SpanGrowth/` (6 files): Cumulative span, eigenvector spreading, trace products
- `RankOne/` (8 files): Rank-one construction and extraction pipeline
- `RectangularSpan/` (4 files): Rectangular span machinery
- `PaperResults/` (6 files): All paper-facing wrappers with descriptive names

**Top-level files**:
- `FittingDecomposition.lean`: Pure algebra, used across subfolders
- `QuantumWielandt.lean`: Top-level assembly

---

## 7. Legacy / Archive Pass

### Create `TNLean/Archive/`

Move these files (they are already excluded from `TNLean.lean` or marked archival):

| Source | Archive destination | Notes |
|--------|-------------------|-------|
| `Channel/PeripheralClosure.lean` | `Archive/PeripheralClosure.lean` | "Legacy wrapper" |
| `MPS/BlockingPeriodicity.lean` | `Archive/BlockingPeriodicity.lean` | "Legacy wrapper" |
| `MPS/BlockingPeriodicityCFII2.lean` | `Archive/BlockingPeriodicityCFII2.lean` | "archival alternate route" |
| `Scratch/BlockSepCounterexample.lean` | `Archive/BlockSepCounterexample.lean` | Documentary |

Add an `Archive/README.md` explaining these are retained for reference but not
part of the active library.

### Audit remaining "legacy" mentions

Several files contain "legacy wrapper" or "legacy compatibility" for internal
theorem aliases. These are fine — they provide API stability within active files.
No action needed beyond the 4 files above.

---

## 8. Large File Splits

Files over 1000 lines that should be split:

### `Wielandt/RectSpanUniversality.lean` (1,892 lines)
→ Split into:
- `RectangularSpan/Universality.lean` (~1000 lines): Core universality proofs
- `RectangularSpan/SharpBackends.lean` (~900 lines): Sharp bound machinery

### `PiAlgebra/CanonicalFormSep.lean` (1,598 lines)
→ Split into:
- `PiAlgebra/CanonicalFormSep.lean` (~800 lines): Separated hypotheses API
- `PiAlgebra/CanonicalFormSepBlock.lean` (~800 lines): Per-block separation

### `Wielandt/Prop3_ac.lean` (1,332 lines)
→ After rename to `Primitivity/ImpliesStronglyIrreducible.lean`, consider splitting
  helper lemmas (sandwich, transfer, spanning) into a `Primitivity/Helpers.lean`.

### `Channel/CyclicDecomposition.lean` (1,339 lines)
→ Consider splitting the three logical steps (unitary normalization, spectral
  projection, corner restriction) into separate files under `Peripheral/`.

### `Spectral/SpectralGapNT.lean` (1,229 lines) and `SpectralGap.lean` (1,175 lines)
→ These are cohesive enough to keep as-is for now, but flag for future review.

---

## 9. Compatibility Shim Strategy

For each renamed file, leave a **shim file** at the old path:

```lean
-- TNLean/Wielandt/Theorem1.lean (SHIM — will be removed in v0.3)
import TNLean.Wielandt.PaperResults.WielandtInequality

-- This file has been moved to TNLean.Wielandt.PaperResults.WielandtInequality.
-- This re-export shim will be removed in a future release.
-- Please update your imports.

#check @qIndex_le_iIndex_of_isPrimitivePaper  -- verify re-export works
```

Shim files should:
1. Import the new location
2. Have a clear deprecation comment
3. Be excluded from the root `TNLean.lean`
4. Be removed after one release cycle

---

## 10. Migration Sequence

Execute in phases to keep the project building at every step:

### Phase 0: Preparation (no file moves)
- [ ] Create `docs/REORGANIZATION_PLAN.md` (this file)
- [ ] Create `TNLean/Archive/` directory with README
- [ ] Verify full `lake build` succeeds

### Phase 1: Archive pass (low risk)
- [ ] Move 4 legacy/archival files to `Archive/`
- [ ] Create shims at old locations
- [ ] Remove `Scratch/` directory
- [ ] Update `TNLean.lean` (already excluded, but verify)
- [ ] `lake build`

### Phase 2: Channel subfolders
- [ ] Create `Channel/{Schwarz,Irreducible,Peripheral,PerronFrobenius,FixedPoint}/`
- [ ] Move files, update imports within moved files
- [ ] Create shims at old locations
- [ ] Update `TNLean.lean` to use new paths
- [ ] `lake build`

### Phase 3: MPS subfolders
- [ ] Create `MPS/{Basic,BNT,CanonicalForm,FundamentalTheorem,Irreducible,Overlap,Structure}/`
- [ ] Move files, update imports
- [ ] Rename `BNTPermutationThm44` → `BNT/PermutationRigidity`
- [ ] Rename `CanonicalFormExistence1606` → `CanonicalForm/Existence`
- [ ] Create shims, update root imports
- [ ] `lake build`

### Phase 4: Wielandt subfolders + paper renames (highest impact)
- [ ] Create `Wielandt/{Primitivity,SpanGrowth,RankOne,RectangularSpan,PaperResults}/`
- [ ] Move and rename all paper-numbered files
- [ ] Create shims at all old locations
- [ ] Update `TNLean.lean` to use new paths
- [ ] `lake build`

### Phase 5: Large file splits (optional, can defer)
- [ ] Split `RectSpanUniversality` (1892 lines)
- [ ] Split `CanonicalFormSep` (1598 lines)
- [ ] Split `Prop3_ac` → `ImpliesStronglyIrreducible` + helpers
- [ ] `lake build`

### Phase 6: Cleanup
- [ ] Remove all shim files
- [ ] Final `lake build`
- [ ] Update blueprint references if any point to old paths
- [ ] Update CI/documentation

---

## Appendix A: Full Old→New Path Mapping

<details>
<summary>Click to expand complete mapping (132 files)</summary>

### Algebra (unchanged)
```
TNLean/Algebra/BlockPermutation.lean         → (no change)
TNLean/Algebra/BlockTriangularTrace.lean     → (no change)
TNLean/Algebra/BurnsideMatrix.lean           → (no change)
TNLean/Algebra/BurnsideTheorem.lean          → (no change)
TNLean/Algebra/GramMatrixLI.lean             → (no change)
TNLean/Algebra/HermitianHelpers.lean         → (no change)
TNLean/Algebra/IrreducibleTensorAction.lean  → (no change)
TNLean/Algebra/MatrixFrobenius.lean          → (no change)
TNLean/Algebra/NewtonGirard.lean             → (no change)
TNLean/Algebra/ProjectionTriangularTrace.lean → (no change)
TNLean/Algebra/ScalarPowerSumIdentity.lean   → (no change)
TNLean/Algebra/SkolemNoether.lean            → (no change)
TNLean/Algebra/TracePairing.lean             → (no change)
```

### Axioms
```
TNLean/Axioms/BrouwerFixedPointDensityMatrices.lean
  → TNLean/Axioms/BrouwerFixedPoint.lean
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
TNLean/Channel/Ergodicity.lean               → TNLean/Channel/FixedPoint/Ergodicity.lean
TNLean/Channel/DSGauge.lean                  → TNLean/Channel/FixedPoint/DSGauge.lean

TNLean/Channel/PeripheralClosure.lean        → TNLean/Archive/PeripheralClosure.lean
```

### MPS
```
TNLean/MPS/Defs.lean                         → (no change, top-level)

TNLean/MPS/Transfer.lean                     → TNLean/MPS/Basic/Transfer.lean
TNLean/MPS/Blocking.lean                     → TNLean/MPS/Basic/Blocking.lean
TNLean/MPS/BlockingTransfer.lean             → TNLean/MPS/Basic/BlockingTransfer.lean
TNLean/MPS/CastLemmas.lean                   → TNLean/MPS/Basic/CastLemmas.lean
TNLean/MPS/CPPrimitive.lean                  → TNLean/MPS/Basic/CPPrimitive.lean
TNLean/MPS/MultiBlock.lean                   → TNLean/MPS/Basic/MultiBlock.lean
TNLean/MPS/TransferNormalization.lean        → TNLean/MPS/Basic/TransferNormalization.lean
TNLean/MPS/TPGaugeFromAdjointFixedPoint.lean → TNLean/MPS/Basic/TPGauge.lean

TNLean/MPS/BNT.lean                          → TNLean/MPS/BNT/Basic.lean
TNLean/MPS/BasisNormal.lean                  → TNLean/MPS/BNT/BasisNormal.lean
TNLean/MPS/BNTConstruction.lean              → TNLean/MPS/BNT/Construction.lean
TNLean/MPS/BNTPermutationThm44.lean          → TNLean/MPS/BNT/PermutationRigidity.lean
TNLean/MPS/BNTPermutationSimple.lean         → TNLean/MPS/BNT/PermutationSimple.lean

TNLean/MPS/CanonicalFormReduction.lean       → TNLean/MPS/CanonicalForm/Reduction.lean
TNLean/MPS/CanonicalFormFromPrimitive.lean   → TNLean/MPS/CanonicalForm/FromPrimitive.lean
TNLean/MPS/CanonicalFormFromPeripheralPrimitive.lean → TNLean/MPS/CanonicalForm/FromPeripheralPrimitive.lean
TNLean/MPS/CanonicalFormExistence1606.lean   → TNLean/MPS/CanonicalForm/Existence.lean
TNLean/MPS/NormalCanonicalFormPipeline.lean  → TNLean/MPS/CanonicalForm/NormalPipeline.lean

TNLean/MPS/FundamentalTheorem.lean           → TNLean/MPS/FundamentalTheorem/Basic.lean
TNLean/MPS/FundamentalTheoremProportional.lean → TNLean/MPS/FundamentalTheorem/Proportional.lean
TNLean/MPS/FundamentalTheoremMulti.lean      → TNLean/MPS/FundamentalTheorem/Multi.lean
TNLean/MPS/FundamentalTheoremFull.lean       → TNLean/MPS/FundamentalTheorem/Full.lean
TNLean/MPS/CoefficientConvergence.lean       → TNLean/MPS/FundamentalTheorem/CoefficientConvergence.lean

TNLean/MPS/IrreducibleFormII.lean            → TNLean/MPS/Irreducible/FormII.lean
TNLean/MPS/IrreducibleAdjoint.lean           → TNLean/MPS/Irreducible/Adjoint.lean
TNLean/MPS/FixedPointInvariantProjection.lean → TNLean/MPS/Irreducible/FixedPointProjection.lean

TNLean/MPS/MPVOverlap.lean                   → TNLean/MPS/Overlap/Basic.lean
TNLean/MPS/CastOverlapDecay.lean             → TNLean/MPS/Overlap/CastDecay.lean
TNLean/MPS/PeripheralToSpectralGap.lean      → TNLean/MPS/Overlap/PeripheralToSpectralGap.lean

TNLean/MPS/BlockPermutationMPS.lean          → TNLean/MPS/Structure/BlockPermutation.lean
TNLean/MPS/InvariantSubspaceDecomp.lean      → TNLean/MPS/Structure/InvariantSubspaceDecomp.lean
TNLean/MPS/LinearExtension.lean              → TNLean/MPS/Structure/LinearExtension.lean
TNLean/MPS/PrimitivityBridge.lean            → TNLean/MPS/Structure/PrimitivityBridge.lean

TNLean/MPS/BlockingPeriodicityCFII_viaAdjoint.lean → TNLean/MPS/Periodicity/CFIIViaAdjoint.lean

TNLean/MPS/BlockingPeriodicity.lean          → TNLean/Archive/BlockingPeriodicity.lean
TNLean/MPS/BlockingPeriodicityCFII2.lean     → TNLean/Archive/BlockingPeriodicityCFII2.lean
```

### PiAlgebra, QPF, Spectral, Topology (unchanged)
```
(all files remain at current paths)
```

### Wielandt
```
TNLean/Wielandt/FittingDecomposition.lean     → (no change, top-level)
TNLean/Wielandt/QuantumWielandt.lean          → (no change, top-level)

TNLean/Wielandt/PrimitivePaper.lean           → TNLean/Wielandt/Primitivity/Defs.lean
TNLean/Wielandt/PrimitiveEquiv.lean           → TNLean/Wielandt/Primitivity/EasyDirections.lean
TNLean/Wielandt/Prop3.lean                    → TNLean/Wielandt/Primitivity/Equivalence.lean
TNLean/Wielandt/Prop3_ac.lean                 → TNLean/Wielandt/Primitivity/ImpliesStronglyIrreducible.lean
TNLean/Wielandt/Prop3_cb.lean                 → TNLean/Wielandt/Primitivity/StronglyIrreducibleToFullRank.lean
TNLean/Wielandt/PrimitiveImpliesIrreducible.lean → TNLean/Wielandt/Primitivity/ImpliesIrreducible.lean
TNLean/Wielandt/PrimitivityNormal.lean        → TNLean/Wielandt/Primitivity/Normal.lean
TNLean/Wielandt/PrimitivityToNormal.lean      → TNLean/Wielandt/Primitivity/ToNormal.lean

TNLean/Wielandt/CumulativeSpan.lean           → TNLean/Wielandt/SpanGrowth/CumulativeSpan.lean
TNLean/Wielandt/CumulativeToWordSpan.lean     → TNLean/Wielandt/SpanGrowth/CumulativeToExact.lean
TNLean/Wielandt/EigenvectorSpreading.lean     → TNLean/Wielandt/SpanGrowth/EigenvectorSpreading.lean
TNLean/Wielandt/InvertibleWordSpanGrowth.lean → TNLean/Wielandt/SpanGrowth/InvertibleWordSpan.lean
TNLean/Wielandt/NonzeroTraceProduct.lean      → TNLean/Wielandt/SpanGrowth/NonzeroTraceProduct.lean
TNLean/Wielandt/WielandtBound.lean            → TNLean/Wielandt/SpanGrowth/WielandtBound.lean

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
TNLean/Wielandt/Lemma2.lean                   → TNLean/Wielandt/PaperResults/EigenvectorSpreadingPaper.lean
TNLean/Wielandt/Lemma2b.lean                  → TNLean/Wielandt/PaperResults/VectorToMatrixSpan.lean
TNLean/Wielandt/Lemma2bCoarse.lean            → TNLean/Wielandt/PaperResults/MatrixSpanExistence.lean
TNLean/Wielandt/Lemma2bExact.lean             → TNLean/Wielandt/PaperResults/MatrixSpanSharpBound.lean
```

</details>

---

## Appendix B: Dependency Impact Analysis

The most disruptive renames from a dependency perspective:

| Old module | # downstream importers | Risk |
|-----------|----------------------|------|
| `Channel.PositiveMap` | 8 | Medium — widely imported base |
| `Channel.Irreducible` | 9 | Medium — widely imported |
| `MPS.Transfer` | 7 | Medium |
| `MPS.Defs` | 8 | **Keep in place** (top-level) |
| `Wielandt.CumulativeSpan` | 4 | Low |
| `Wielandt.EigenvectorSpreading` | 3 | Low |
| `Wielandt.Lemma2b` | 4 | Low |
| `Wielandt.Prop3` | 5 | Low |

Shim files eliminate all breaking changes. The only modification needed in
downstream files during the transition is updating to new import paths, which
can happen incrementally.

---

## Appendix C: What We're NOT Changing

- **`TNLean/Algebra/`**: 13 files, well-named, no action.
- **`TNLean/PiAlgebra/`**: 4 files, good names (consider splitting CanonicalFormSep later).
- **`TNLean/QPF/`**: 3 files, clean.
- **`TNLean/Spectral/`**: 9 files, acceptable (SpectralGap/NT are large but cohesive).
- **`TNLean/Topology/`**: 4 files, clean.
- **Internal theorem/definition names**: This plan is about *file organization*
  only. Renaming individual theorems/definitions is a separate effort.

---

*End of plan. Ready for review before execution.*
