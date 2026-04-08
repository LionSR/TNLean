# Lean Code Quality Issues — Follow-up from Blueprint v4 Review

**Date:** April 8, 2026  
**Source:** Parallel codex audits of all TNLean/ directories  
**Status:** Follow-up issues for separate PRs (not part of PR #507)

## Global Metrics

- **Total Lean code:** ~78K lines across 200+ files
- **Total sorry count:** ~33 actual proof-level sorry's (excluding comments/docstrings)
- **Axiom declarations:** 1 (`strong_subadditivity` in `TNLean/Axioms/Entropy.lean`)
- **Largest files:** Full.lean (1344), CyclicDecomposition.lean (1426), SpectralGapNT.lean (1275), Determinant.lean (1202), Assembly.lean (1121), SpectralGap.lean (1113)

## Priority 1: Structural Issues

### 1.1 Files over 1000 lines — should be split

| File | Lines | Issue |
|------|-------|-------|
| `MPS/FundamentalTheorem/Full.lean` | 1344 | Contains two monolithic proofs of ~838 and ~339 lines |
| `Channel/Peripheral/CyclicDecomposition.lean` | 1426 | Single-file cyclic decomposition theory |
| `Spectral/SpectralGapNT.lean` | 1275 | Non-TI spectral gap |
| `Channel/Determinant.lean` | 1202 | Channel determinant theory |
| `MPS/CanonicalForm/Assembly.lean` | 1121 | Mixes ≥4 responsibilities |
| `Spectral/SpectralGap.lean` | 1113 | TI spectral gap |

### 1.2 Layer inversion in MPS dependency graph

The canonical-form and fundamental-theorem layers are tangled:
- `CanonicalForm/NormalReduction.lean` imports `FundamentalTheorem/TransferNormalization`
- `CanonicalForm/BNTGrouping.lean` imports `FundamentalTheorem/SectorDecomposition`
- `CanonicalForm/EqualNormBridge.lean` imports `FundamentalTheorem/Proportional`
- `CanonicalForm/Assembly.lean` imports `FundamentalTheorem/Full`
- `FundamentalTheorem/PeriodicOverlap.lean` imports `CanonicalForm/Assembly`

This creates a dependency knot. Refactoring suggestion: extract shared infrastructure into a separate layer.

### 1.3 PEPS scaffold is purely sorry

`TNLean/PEPS/FundamentalTheorem.lean`: 6 sorry's, 8 TODO markers. The file is imported at the project root but provides no proved theorems. Consider gating the import behind a feature flag or moving to a separate `PEPS.Stub` module.

## Priority 2: Sorry Clusters

### 2.1 PeriodicOverlap.lean — 7 sorry's

All 7 are in `TNLean/MPS/FundamentalTheorem/PeriodicOverlap.lean` (774 lines). These are the periodic fundamental theorem's sector-matching theorems. None appear trivially closable.

### 2.2 ParentHamiltonian — 5 sorry's across 3 files

- `Martingale.lean`: 1 sorry (`parentHamiltonian_gapped`)
- `UniqueGroundState.lean`: 4 sorry's (chainGroundSpace normal, unique GS injective/normal)
- `DegenerateGS.lean`: 1 sorry (`parentHamiltonian_gs_eq_bnt_span`)

The `UniqueGroundState` sorry's have a common root: `WrappingWindow.lean` fails to elaborate, blocking the chain-ground-space equality.

### 2.3 Wedderburn — 3 sorry's

`Channel/FixedPoint/WedderburnDecomp.lean`: semisimplicity, abstract Wedderburn-Artin, concrete block decomposition. Blocked on Jacobson radical theory for *-algebras.

### 2.4 Operator convexity — 3 sorry's

`Channel/Schwarz/OperatorConvexity.lean`: Jensen inequalities for rpow and log. Not imported by semigroup files, so isolated.

### 2.5 AndoLieb — 3 sorry's

`Channel/Schwarz/AndoLieb.lean`: Ando-Lieb theorem and operator monotone characterizations. Placeholder file.

### 2.6 RFP structural — 1 sorry

`MPS/RFP/StructuralForm.lean`: `rfp_nt_structural` — rank-1 characterization of idempotent CPTP maps.

## Priority 3: Code Quality

### 3.1 Bare `simp` (no `only` qualifier) — top offenders

- `PosDef.lean`: 19 bare simp calls
- `Uniqueness.lean`: 12 bare simp calls
- Various other files: 3-5 each

### 3.2 Stale TODO comments (20 total)

Most are in `ParentHamiltonian/` (5) and `PEPS/` (8). These should be converted to GitHub issues or closed.

### 3.3 Removable imports (confirmed by elaboration)

- `CanonicalForm/CyclicSectors.lean`: `Mathlib.Analysis.Matrix.Spectrum` and `Mathlib.Logic.Equiv.Sum` are unused

### 3.4 Long proofs needing factoring

- `FundamentalTheorem/Full.lean`: two proofs of ~838 and ~339 lines
- `Algebra/ProjectionTriangularTrace.lean`: long proof bodies
- `Algebra/BurnsideTheorem.lean`: long proof bodies
- `MPS/Overlap/PeripheralToSpectralGap.lean`: long proof body
- `PiAlgebra/CanonicalFormSepAux.lean`: long proof body

### 3.5 Repeated proof boilerplate

- `Full.lean`: `convert (...).norm using 1; simp only [norm_one/norm_zero]` pattern repeated many times
- `Chain/Defs.lean` and `Periodic/Defs.lean`: relation-law boilerplate duplicated

### 3.6 Stale comment in NormalReduction.lean:139

Says `exists_tp_gauge_blockwise` is unused, but it IS used later in the same file.

## Priority 4: Naming Conventions

Mixed camelCase/snake_case in theorem names throughout `MPS/`:
- `fundamentalTheorem_singleBlock` (camel+snake)
- `sameMPV_of_sameMPVFrom_of_injective` (acronym case varies)
- `exists_CFII_data_of_TP_of_isIrreducibleTensor` (screaming caps)

Mathlib convention: all snake_case. Fixing this would be a large refactor.

## Priority 5: Unsound Import Contamination

- `Channel/Schwarz/OperatorMonotone.lean` imports `OperatorConvexity` (3 sorry's) — makes some proved-looking corollaries only conditionally sound
- `Channel/WolfChapter6Index.lean` is documentation-only but imports `WedderburnDecomp` (3 sorry's) — unnecessary contamination

## Priority 6: Monster Proofs (>200 lines)

| Proof | File | Lines |
|-------|------|-------|
| `eigenvector_gives_gauge` | SpectralGap.lean:394-978 | 585 |
| `exists_cyclic_projections_of_peripheral_unitary` | CyclicDecomposition.lean:537-1100 | 564 |
| `eigenvector_gives_gauge_of_irreducible_TP` | SpectralGapNT.lean:87-609 | 523 |
| `dim_eq_of_modulus_one_eigenvector_of_irreducible_TP` | SpectralGapNT.lean:751-1203 | 453 |
| `finrank_traceless_blockUT_add_D_le` | RelaxationConditions.lean:345-678 | 334 |
| `blockForm_nonneg_of_scalarPSD_of_commuting` | PositiveOnAbelian.lean:458-731 | 274 |
| `heisenberg_dual_multiplicative` | Determinant.lean:649-917 | 269 |
| `spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp` | SpectralRadius.lean:208-471 | 264 |

## Priority 7: Copy-Paste Clusters

1. **CP→Kraus→irreducible-tensor boilerplate**: duplicated across `Irreducible/PerronFrobenius.lean`, `Irreducible/FromSpectral.lean`, `Irreducible/SpectralRadius.lean`
2. **Support-projection invariance proof**: duplicated between `FixedPoint/StationarySupport.lean` and `Semigroup/ReducibleQDS/FixedDensity.lean`
3. **Gauge-rigidity architecture**: SpectralGap, SpectralGapRect, SpectralGapNT repeat the same structure in square/rectangular/dimension-mismatch variants
4. **Kraus-map linearity APIs**: re-stated locally in `FixedPoint/Algebra`, `Schwarz/Basic`, `Schwarz/MultiplicativeDomainFull`
5. **Relation-law boilerplate**: duplicated between `Chain/Defs.lean` and `Periodic/Defs.lean`

## Priority 8: Dead Code / Stale Artifacts

- `Wielandt/WielandtBound.lean:264`: `: True := trivial` theorem anchoring prose
- `Wielandt/RectangularSpan/Universality.lean:836`: same pattern
- `CanonicalForm/NormalReduction.lean:139`: stale "unused" comment (declaration IS used)

## Suggested Follow-up PRs (ordered by ROI)

1. **Split CyclicDecomposition.lean** (564-line proof!) — highest single-file ROI
2. **Split Full.lean** — extract two monolithic proofs into helper chains
3. **Close WrappingWindow elaboration** — unblocks 4 ParentHamiltonian sorry's
4. **Factor CP→Kraus→irreducible-tensor boilerplate** — DRY the Irreducible trilogy
5. **Factor gauge-rigidity core** — share across SpectralGap/NT/Rect variants
6. **Remove unused imports** — `CyclicSectors.lean` confirmed; check others
7. **Convert 20 TODO comments to GitHub issues** — across 6 files
8. **Squeeze simp** — SpectralGapNT (156 bare), CyclicDecomposition (119), SpectralGap (71)
9. **Untangle CanonicalForm ↔ FundamentalTheorem imports** — architectural
10. **Remove sorry import contamination** — WolfChapter6Index doesn't need WedderburnDecomp
