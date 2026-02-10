---
title: "Lean-QuantumInfo deep analysis: CP map infrastructure inventory"
date: 2026-02-09
author: AI research assistant (search agent)
purpose: >
  Exhaustive file-by-file examination of Timeroot/Lean-QuantumInfo
  (20,434 lines, 1,059 theorems).  Catalogs every definition and theorem
  in the CPTPMap module, HermitianMat infrastructure, and ForMathlib
  extensions.  Assesses version gap (v4.24→v4.27), sorry status on the
  critical path, and cherry-pick / guided-rewrite strategies.
---

# Deep Analysis: Lean-QuantumInfo for MPSLean's Spectral Gap
## Exhaustive File-by-File Examination Report

**Date**: February 9, 2026  
**Analyst**: AI Research Assistant  
**Subject**: https://github.com/Timeroot/Lean-QuantumInfo  
**Purpose**: Determine what can be leveraged for closing MPSLean's spectral gap

---

## Executive Summary

**Lean-QuantumInfo** is the most substantial Lean 4 formalization of quantum information theory available today: 20,434 lines, 1,059 theorems, 248 definitions, MIT license. Its completely positive trace-preserving (CPTP) map infrastructure — including **sorry-free** proofs of **Choi's theorem** and the **Kraus decomposition** — directly matches MPSLean's transfer operator framework. However, the repository is **3 minor Lean versions behind** MPSLean (v4.24.0 vs v4.27.0) and critically **lacks all spectral theory for CP maps** (no quantum Perron-Frobenius, no fixed point theory, no convergence results).

**Bottom line**: Saves ~2-3 weeks on CP map foundations via guided rewriting; the hard part (spectral gap, ~6-8 weeks) must be built from scratch. Combined with HopfieldNet's classical PF (same Lean version, direct import), total effort drops from ~15 weeks to ~10 weeks.

---

## 1. Repository Overview

| Property | Value |
|----------|-------|
| **URL** | https://github.com/Timeroot/Lean-QuantumInfo |
| **Lean version** | v4.24.0 **(our: v4.27.0 — gap!)** |
| **Mathlib revision** | `f897ebcf72cd16f` **(ours: `910dac3f6e` — different!)** |
| **Total LoC** | 20,434 |
| **Theorems** | 1,059 |
| **Definitions** | 248 |
| **Sorries** | 105 total (only 13 in CPTPMap, only 3 on our critical path) |
| **License** | MIT |
| **Activity** | 343 commits, 101 stars, 24 forks, 8 contributors |
| **Focus** | Generalized Quantum Stein's Lemma |

### Directory Structure
```
QuantumInfo/
├── CPTPMap/          ← 5 files, 2,615 lines (OUR PRIMARY INTEREST)
│   ├── MatrixMap.lean
│   ├── Unbundled.lean
│   ├── Bundled.lean
│   ├── CPTP.lean
│   └── Dual.lean
├── HermitianMat/     ← 10 files, 3,316 lines (supporting infrastructure)
├── MState.lean       ← 1,441 lines (quantum states)
├── Pinching.lean     ← 587 lines (block-diagonal projections)
├── Entropy.lean      ← 467 lines (von Neumann entropy)
├── Capacity.lean     ← 259 lines
├── TraceNorm.lean    ← 116 lines
├── POVM.lean         ← 244 lines
├── Measurement.lean  ← 269 lines
└── ...
ForMathlib/
├── Matrix.lean       ← 1,342 lines (PSD, eigenvalues, Kronecker)
├── Isometry.lean     ← 633 lines (simultaneous diagonalization!)
└── ...
```

---

## 2. CPTPMap Module — Complete Inventory

### 2.1 MatrixMap.lean (390 lines, 2 sorries)

**Core type**: `MatrixMap A B R := Matrix A A R →ₗ[R] Matrix B B R`

This is **exactly** our transfer map type:
```lean
-- Lean-QuantumInfo:
MatrixMap dIn dOut ℂ = Matrix dIn dIn ℂ →ₗ[ℂ] Matrix dOut dOut ℂ

-- MPSLean:
transferMap : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ
```

#### Every definition and theorem:

| Name | Type | Status | Description |
|------|------|--------|-------------|
| `MatrixMap` | def | ✅ | Core type alias |
| `choi_matrix` | def | ✅ | Choi-Jamiołkowski matrix J(Φ) |
| `of_choi_matrix` | def | ✅ | Inverse: matrix → map |
| `map_choi_inv` | theorem | ✅ | of_choi(choi(Φ)) = Φ |
| `choi_map_inv` | theorem | ✅ | choi(of_choi(J)) = J |
| `choi_equiv` | def | ✅ | `MatrixMap A B R ≃ₗ[R] Matrix (A×B) (A×B) R` |
| `toMatrix` | def | ✅ | Transfer matrix representation |
| `of_kraus` | def | ✅ | `of_kraus Ks X = Σᵢ Kᵢ * X * Kᵢ†` |
| `exists_kraus` | theorem | ✅ | Every map admits Kraus form (from Choi) |
| `submatrix` | def | ✅ | Restriction to subspace |
| `kron` | def | ✅ | Kronecker product of maps |
| `add_kron` | theorem | ✅ | (Φ+Ψ)⊗Γ = Φ⊗Γ + Ψ⊗Γ |
| `kron_add` | theorem | ✅ | Φ⊗(Ψ+Γ) = Φ⊗Ψ + Φ⊗Γ |
| `smul_kron` | theorem | ✅ | (cΦ)⊗Ψ = c(Φ⊗Ψ) |
| `kron_id_id` | theorem | ✅ | id⊗id = id |
| `kron_comp_distrib` | theorem | ✅ | (Φ₁∘Φ₂)⊗(Ψ₁∘Ψ₂) = (Φ₁⊗Ψ₁)∘(Φ₂⊗Ψ₂) |
| `kron_map_of_kron_state` | theorem | ✅ | (Φ⊗Ψ)(A⊗B) = Φ(A)⊗Ψ(B) |
| `piKron` | def | ✅ | Finitely-indexed tensor products |

**Sorries**: 2 (in minor Kronecker lemmas, not on our critical path)

### 2.2 Unbundled.lean (757 lines, 1 sorry) — **MOST CRITICAL FILE**

Every predicate and theorem for CP map properties:

#### Predicates defined:
| Name | Definition |
|------|-----------|
| `IsTracePreserving` | ∀X, Tr(Φ(X)) = Tr(X) |
| `Unital` | Φ(I) = I |
| `IsHermitianPreserving` | ∀X, Φ(X†) = Φ(X)† |
| `IsPositive` | ∀X≥0, Φ(X)≥0 |
| `IsCompletelyPositive` | ∀n, (Φ⊗id_n) is positive |

#### Key theorems (all sorry-free unless noted):

| Name | Statement | Sorries |
|------|-----------|---------|
| `IsTracePreserving_iff_trace_choi` | TP ↔ partial trace condition on Choi matrix | 0 |
| **`choi_PSD_iff_CP_map`** | **Φ is CP ↔ Choi(Φ) is PSD** (Choi's theorem) | **0** |
| **`exists_kraus_of_choi_PSD`** | **Choi PSD → ∃ Kraus operators** | **0** |
| `of_kraus_CP` | Kraus operators define a CP map | 0 |
| `of_kraus_isTracePreserving` | Σ Kᵢ† Kᵢ = I ↔ Kraus map is TP | 0 |
| `of_kraus_isCompletelyPositive` | Kraus operators give CP map | 0 |
| `conj_isPositive` | Conjugation (X ↦ AXA†) is positive | 0 |
| `conj_isCompletelyPositive` | Conjugation is CP | 0 |
| `IsPositive.comp` | Positive ∘ Positive = Positive | 0 |
| `IsCompletelyPositive.comp` | CP ∘ CP = CP | 0 |
| `IsTracePreserving.comp` | TP ∘ TP = TP | 0 |
| `IsPositive.add` | Positive + Positive = Positive | 0 |
| `IsCompletelyPositive.add` | CP + CP = CP | 0 |
| `IsCompletelyPositive.smul` | c≥0 → cΦ CP if Φ CP | 0 |
| `kron_isPositive` | Positive ⊗ Positive = Positive | 0 |
| `kron_isCompletelyPositive` | CP ⊗ CP = CP | 0 |
| `kron_isTracePreserving` | TP ⊗ TP = TP | 0 |

**The one sorry** is in a minor lemma not on our path.

### 2.3 Bundled.lean (435 lines, 0 sorries)

Full bundled type hierarchy with typeclasses:

```
HPMap   ← Hermitian-preserving maps
  ↓
PMap    ← Positive maps
  ↓
CPMap   ← Completely positive maps  ← CPUMap (CP + Unital)
  ↓                                      ↑
CPTPMap ← CP + TP (quantum channels)     |
  ↑                                      |
PTPMap  ← Positive + TP                  |
  ↑                                      |
TPMap   ← Trace-preserving         UnitalMap
```

All types have `FunLike`, `LinearMapClass` instances. The `CPTPMap` type is our natural home for the transfer operator.

Key constructors:
- `of_kraus_CPMap`: Kraus operators → CPMap
- `of_kraus_CPTPMap`: Kraus operators + TP condition → CPTPMap

### 2.4 CPTP.lean (528 lines, 7 sorries)

Channel-level operations:

| Name | Type | Status |
|------|------|--------|
| `CPTPMap.compose` | CPTP ∘ CPTP → CPTP | ✅ |
| `CPTPMap.id` | Identity channel | ✅ |
| `CPTPMap.replacement` | Replacement channel | ✅ |
| `CPTPMap.prod` | Tensor product channel | ✅ |
| `CPTPMap.ofUnitary` | Unitary channel | ✅ |
| `CPTPMap.ofEquiv` | Relabeling channel | ✅ |
| `CPTPMap.SWAP` | Swap channel | ✅ |
| `CPTPMap.assoc` / `assoc'` | Associativity | ✅ |
| `CPTPMap.traceLeft` | Partial trace (left) | ✅ |
| `CPTPMap.traceRight` | Partial trace (right) | ✅ |
| `CPTPMap.piProd` | n-fold tensor | 1 sorry (TP) |
| `CPTPMap.purify` | Stinespring purification | 1 sorry |
| `CPTPMap.complementary` | Complementary channel | ✅ |
| `IsDegradable` / `IsAntidegradable` | Degradability | ✅ defs |
| `instMixable` | Convex structure | ✅ |
| `instTop` | Topology on channels | ✅ |

**7 sorries** total: `piProd` TP (1), `fin_1_piProd` (1), `exists_purify` (1), 4 minor.

### 2.5 Dual.lean (505 lines, 3 sorries)

The dual (adjoint) of a matrix map, defined via `LinearMap.dualMap`:

| Name | Type | Status |
|------|------|--------|
| `dual` | MatrixMap → MatrixMap | ✅ |
| `Dual.trace_eq` | Tr[A·Φ(B)] = Tr[Φ*(A)·B] | **1 sorry** |
| `IsHermitianPreserving.dual` | HP → dual HP | **1 sorry** |
| `IsPositive.dual` | Positive → dual Positive | **1 sorry** |
| `dual_Unital` | TP → dual Unital | ✅ |
| `dual_unique` | Dual is unique | ✅ |
| `dual_choi_matrix` | Choi(Φ*) = transpose(Choi(Φ)) | ✅ |
| `dual_dual` | (Φ*)* = Φ | ✅ |
| `dual_kron` | (Φ⊗Ψ)* = Φ*⊗Ψ* | ✅ |
| `IsCompletelyPositive.dual` | CP → dual CP | ✅ |

**Alternative sorry-free path**: `HPMap.hermDual` uses the Hilbert-Schmidt inner product:
| Name | Status |
|------|--------|
| `HPMap.hermDual` | ✅ |
| `HPMap.inner_hermDual` | ✅ |
| `HPMap.hermDual_hermDual` | ✅ |
| `MatrixMap.IsPositive.hermDual` | ✅ |
| `HPMap.hermDual_Unital` | ✅ |

---

## 3. Supporting Infrastructure — Complete Inventory

### 3.1 HermitianMat/ (10 files, 3,316 lines, 4 sorries)

**Basic.lean** (371 lines, 0 sorries):
- `HermitianMat` type = bundled self-adjoint matrix
- `toMat`, `conj`, `conjLinear`, `lin` (ContinuousLinearMap)
- `eigenspace`, `ker`, `support` (= ⨆ nonzero eigenspaces)
- `ker_orthogonal_eq_support`
- `diagonal`, `kronecker` with algebra
- `spectrum_prod` (for products)

**CFC.lean** (698 lines, 4 sorries):
- Continuous functional calculus: define f(A) for continuous f
- `cfc_toMat`, `cfc_reindex`, `cfc_eigenvalues`
- `coe_cfc_mul`, `cfc_sq`, `zero_le_cfc`
- `cfc_PosDef`, `rpow`/`pow_eq_cfc`, `rpow_mul`, `conj_rpow`
- `log`, `integral_cfc_eq_cfc_integral`
- 4 sorries in advanced operator inequality proofs

**CfcOrder.lean** (294 lines, 0 sorries):
- `cfc_le_cfc_of_commute_monoOn`
- `log_le_log_of_commute`, `exp_le_exp_of_commute`
- `sandwich_identity`, `sandwich_le_one`
- Various `rpow` ordering lemmas

**Inner.lean** (500 lines, 0 sorries):
- Hilbert-Schmidt inner product on HermitianMat
- `inner_eq_trace_mul`, `inner_comm`
- `inner_self_nonneg`, `inner_ge_zero` (for PSD)
- `inner_mono`
- **Complete inner product space structure**: `InnerProductCore`, `instNormedGroup`, `instInnerProductSpace`, `CompleteSpace`, `OrderClosedTopology`
- `CompactIccSpace`, `unitInterval_IsCompact`

**Jordan.lean** (151 lines, 0 sorries):
- `symmMul` (Jordan product A∘B = (AB+BA)/2)
- Commutation lemmas

**Log.lean** (646 lines, 0 sorries):
- `log_zero`, `log_one`, `log_smul`
- `inv_antitone`, `logApprox_mono`, `log_mono`
- `inv_convex`, `logApprox_concave`
- **`log_concave`** — Operator concavity of log (major result!)
- `log_kron`, `log_conj_unitary`

**Order.lean** (137 lines, 0 sorries):
- Loewner order: `le_iff`, `zero_le_iff`
- `le_iff_mulVec_le`, `ZeroLEOneClass`

**Proj.lean** (281 lines, 0 sorries):
- Spectral projections: `proj_le`, `proj_lt`
- `posPart`/`negPart` (positive/negative parts)
- `posPart_add_negPart` (Jordan decomposition A = A⁺ - A⁻)
- `posPart_mul_negPart` = 0

**Reindex.lean** (86 lines, 0 sorries): Dimension relabeling

**Trace.lean** (152 lines, 0 sorries):
- `trace`, `sum_eigenvalues_eq_trace`
- `trace_kronecker`, `FiniteDimensional`

### 3.2 ForMathlib/Matrix.lean (1,342 lines, 0 sorries)

Upstream-quality matrix lemmas:
- `sum_eigenvalues_eq_trace`
- `kroneckerMap_IsHermitian`, `PosSemidef_kronecker`
- `outer_self_conj`, `convex_cone`
- `PosSemidef.traceLeft`/`traceRight`
- `nonneg_iff_eigenvalue_nonneg`
- `trace_monotone`, `diagonal_monotone`
- `le_smul_one_of_eigenvalues_iff`
- `traceLeft`/`traceRight` definitions
- `PosDef.kron`, `PosDef.submatrix`, `PosDef.Convex`
- `charpoly_roots_eq_eigenvalues`
- `cfc_eigenvalues`, `cfc_diagonal`
- **`spectrum_prod`** — spectrum of A⊗B = spectrum(A) × spectrum(B)
- `PosSemidef.pow_add`, `iInf_eigenvalues_le`

### 3.3 ForMathlib/Isometry.lean (633 lines, 0 sorries)

- `Matrix.Isometry` — isometric matrices
- **`Matrix.sharedEigenbasis`** — simultaneous diagonalization of commuting Hermitian matrices
- `sharedEigenvalueA`/`B`, `mulVec_sharedEigenbasisA`/`B`
- **`Commute.exists_unitary`** — commuting Hermitians are simultaneously diagonalizable

**Highly relevant**: If the transfer operator commutes with block-diagonal projections, this provides the simultaneous eigenbasis.

### 3.4 Pinching.lean (587 lines, 0 sorries)

Block-diagonal projection channels:
- `pinching_kraus` — Kraus operators for pinching = eigenspace projectors
- `pinching_map` — Pinching is CPTP
- `pinching_self` — σ is a fixed point of E_σ
- `pinching_idempotent` — E_σ² = E_σ
- `pinching_commutes` — E_σ(ρ) commutes with σ
- `pinching_bound` — ρ ≤ |spec(σ)| · E_σ(ρ)
- `pinching_map_ker_le` — ker(E_σ(ρ)) ⊆ ker(ρ)
- `ker_le_ker_pinching_map_ker`
- `pinching_pythagoras` — D(ρ‖σ) = D(ρ‖E_σ(ρ)) + D(E_σ(ρ)‖σ)
- `HermitianMat.ker_add`/`ker_sum`/`ker_conj`

**Relevant**: Pinching is exactly the block-diagonal projection operation that appears in the multi-block MPS analysis.

### 3.5 MState.lean (1,441 lines, 0 sorries)

Mixed quantum states (PSD + trace 1):
- `MState`, `pure`, `spectrum` (as Distribution)
- `spectralDecomposition` — every MState = Σ pᵢ |ψᵢ⟩⟨ψᵢ|
- `prod`, `traceLeft`/`traceRight`
- `IsSeparable`, `purify`
- `SWAP`/`assoc`

### 3.6 Other Files (not on critical path)

| File | Lines | Sorries | Content |
|------|-------|---------|---------|
| Entropy.lean | 467 | 18 | Von Neumann entropy, strong subadditivity |
| Capacity.lean | 259 | 6 | Quantum capacity, LSD theorem |
| TraceNorm.lean | 116 | 7 | Trace norm |
| POVM.lean | 244 | 7 | Measurements |
| Measurement.lean | 269 | 11 | Quantum measurements |
| ResourceTheory/ | 3,380 | 8 | Quantum Stein's Lemma |

---

## 4. Type Compatibility Analysis

### Exact Match: MatrixMap ↔ transferMap

```lean
-- Lean-QuantumInfo
def MatrixMap (A B : Type*) (R : Type*) := Matrix A A R →ₗ[R] Matrix B B R

-- MPSLean (endomorphism case, A = B)
noncomputable def transferMap (A : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ
```

Both are `ℂ`-linear maps on square complex matrices. The `MatrixMap (Fin D) (Fin D) ℂ` specialization matches our endomorphism case exactly.

### Immediate Application: Our Transfer Map IS Kraus-form

MPSLean defines:
```
E_A(X) = ∑ᵢ Aᵢ * X * Aᵢ†
```

Lean-QuantumInfo's `of_kraus` is:
```
of_kraus Ks X = ∑ᵢ Kᵢ * X * Kᵢ†
```

**Identification**: Our `Aᵢ` are exactly the Kraus operators. This immediately gives:
- `of_kraus_CP` → **E_A is completely positive**
- `of_kraus_isTracePreserving` → **If Σᵢ Aᵢ† Aᵢ = I then E_A is trace-preserving** (this IS the normalization condition in MPS)

### What This Unlocks

Showing E_A is CPTP is a key step because:
1. CPTP maps preserve PSD ordering → E_A maps PSD cone to itself
2. TP ensures spectral radius ≤ 1 (since ‖E_A‖ = 1 for TP)
3. CP structure → the Choi matrix T = Σᵢ Aᵢ ⊗ Āᵢ is PSD
4. PSD Choi matrix → real nonneg structure after vectorization
5. This is the bridge to classical Perron-Frobenius!

---

## 5. Gap Analysis: What Exists vs. What We Need

### ✅ AVAILABLE in Lean-QuantumInfo

| What | Where | Effort to port |
|------|-------|---------------|
| Transfer operator is CP (via Kraus) | Unbundled.lean | 1-2 days |
| Choi matrix is PSD ↔ CP | Unbundled.lean | 3-5 days |
| Kraus decomposition from Choi | Unbundled.lean | 2-3 days |
| TP condition (Σ K†K = I) | Unbundled.lean | 1 day |
| Choi-Jamiołkowski isomorphism | MatrixMap.lean | 2-3 days |
| Transfer matrix representation | MatrixMap.lean | 1-2 days |
| Channel composition/tensor | CPTP.lean | 2-3 days |
| Pinching (block projection) channels | Pinching.lean | 3-5 days |
| PSD cone structure | ForMathlib/Matrix.lean | 2-3 days |
| Spectrum of tensor products | ForMathlib/Matrix.lean | 1-2 days |
| Simultaneous diagonalization | ForMathlib/Isometry.lean | 2-3 days |
| Hermitian mat inner product | HermitianMat/Inner.lean | 2-3 days |
| TP ↔ Unital duality | Dual.lean | 2-3 days |

**Total available infrastructure**: ~2,500 lines covering ~3-4 weeks of work.

### ❌ MISSING — Must Build From Scratch

| What | Difficulty | Estimated effort |
|------|-----------|-----------------|
| **Eigenvalues of CP maps (as superoperators)** | Hard | 2-3 weeks |
| **Fixed point theory for channels** | Hard | 2-3 weeks |
| **Spectral radius of CP maps** | Medium | 1-2 weeks |
| **Quantum Perron-Frobenius theorem** | Very Hard | 3-5 weeks |
| **Irreducibility criteria for CP maps** | Hard | 1-2 weeks |
| **Vectorization map (CP → matrix)** | Medium | 1-2 weeks |
| **Real representation of PSD-preserving map** | Hard | 1-2 weeks |
| **Block separation lemma** | Medium | 1-2 weeks |
| **Convergence of iterated channels** | Medium | 1-2 weeks |
| **Ergodic decomposition** | Hard | 2-3 weeks |

**Total missing**: The entire spectral theory layer, ~6-10 weeks.

---

## 6. Version Compatibility and Integration Strategy

### The Version Gap Problem

| Component | Lean-QuantumInfo | MPSLean |
|-----------|-----------------|---------|
| Lean | v4.24.0 | v4.27.0 |
| Mathlib | `f897ebcf72cd` | `910dac3f6e7f` |

Unlike HopfieldNet (which shares our exact versions), Lean-QuantumInfo **cannot be added as a Lake dependency**. The Mathlib revision difference means:
- API names may have changed
- Lemma signatures may differ
- Import paths may have been reorganized
- Typeclass instances may work differently

### Integration Options

**Option A: Cherry-Pick and Port** (~2-3 weeks)
- Extract the ~600 lines we need from CPTPMap/
- Update all Mathlib API calls to v4.27.0
- Fix any typeclass resolution issues
- Pro: Gets exact proved code
- Con: Tedious version migration, may break unexpectedly

**Option B: Guided Rewrite** (~2-3 weeks, **RECOMMENDED**)
- Use Lean-QuantumInfo as a reference/blueprint
- Rewrite each definition/theorem from scratch for v4.27.0
- Can simplify and specialize to our setting (Fin D, ℂ)
- Pro: Clean code, no porting issues, can tailor to our needs
- Con: Re-proving everything (but with a working template)

**Option C: Contribute Version Bump Upstream** (~1 week of effort + wait time)
- Help upgrade Lean-QuantumInfo to v4.27.0
- Then add as Lake dependency
- Pro: Everyone benefits, ongoing sync
- Con: Requires maintainer cooperation, may take weeks to merge
- Note: Alex Meiburg (maintainer) is active

**Recommendation**: Option B for immediate progress; Option C as parallel effort.

---

## 7. Combined Architecture: All Resources

### Three-Source Strategy

```
┌──────────────────────────────────────────────────────────┐
│                    MPSLean (v4.27.0, Mathlib 910dac3f)   │
│                                                          │
│  ┌─────────────────┐  ┌─────────────────────────────┐   │
│  │ HopfieldNet      │  │ New Code (v4.27.0 native)   │   │
│  │ (Lake dependency)│  │                             │   │
│  │ Same versions!   │  │ CP Map Basics               │   │
│  │                  │  │ (guided by Lean-QuantumInfo) │   │
│  │ Provides:        │  │ - Kraus → CP proof          │   │
│  │ ✅ PF for stoch. │  │ - TP condition              │   │
│  │ ✅ Spectral dom. │  │ - Choi matrix (if needed)   │   │
│  │ ✅ Unique pos.   │  │                             │   │
│  │   eigenvector    │  │ Vectorization Bridge        │   │
│  │ ✅ Convergence   │  │ - E_A → Σ Aᵢ⊗Āᵢ           │   │
│  │                  │  │ - PSD → nonneg entries      │   │
│  │                  │  │ - CP irreducibility         │   │
│  └────────┬─────────┘  │                             │   │
│           │             │ Apply Classical PF          │   │
│           └─────────────│ - dominant eigenvalue = 1   │   │
│                         │ - spectral gap > 0         │   │
│                         │ - unique fixed point        │   │
│                         │                             │   │
│                         │ Block Separation            │   │
│                         │ - multi-block convergence   │   │
│                         │ - E_A^N contracts off-diag  │   │
│                         └─────────────────────────────┘   │
└──────────────────────────────────────────────────────────┘
```

### Effort Breakdown

| Component | Source | Effort | New Lines |
|-----------|--------|--------|-----------|
| Classical Perron-Frobenius | HopfieldNet (import) | 1 week setup | 0 |
| CP map foundations | Guided rewrite from L-QI | 2-3 weeks | 400-600 |
| Vectorization/Choi bridge | New code | 1-2 weeks | 200-400 |
| Irreducibility bridge | New code (HARDEST) | 2-4 weeks | 300-500 |
| Apply classical PF | New + HopfieldNet | 1 week | 100-200 |
| Block separation lemma | New code | 1-2 weeks | 100-200 |
| **TOTAL** | | **8-12 weeks** | **1,100-1,900** |

### Comparison: Without Community Resources

| Component | Effort | Lines |
|-----------|--------|-------|
| Classical PF from scratch | 6-8 weeks | 2,000-3,000 |
| CP map basics from scratch | 3-4 weeks | 600-800 |
| Bridge + block separation | 4-6 weeks | 500-900 |
| **TOTAL** | **13-18 weeks** | **3,100-4,700** |

### Net Savings: ~5-6 weeks and ~2,000 lines

---

## 8. Sorry Analysis on Critical Path

### CPTPMap/ (13 total sorries)

| File | Sorry | On our path? | Workaround |
|------|-------|-------------|------------|
| MatrixMap.lean | 2 (kron lemmas) | ❌ | N/A |
| Unbundled.lean | 1 (minor) | ❌ | N/A |
| Bundled.lean | 0 | ✅ all proved | — |
| CPTP.lean | 7 (piProd, purify, etc.) | ❌ | N/A |
| Dual.lean | `trace_eq` | ⚠️ maybe | Use `hermDual` instead (sorry-free) |
| Dual.lean | `IsHP.dual` | ⚠️ maybe | Use `hermDual` instead (sorry-free) |
| Dual.lean | `IsPos.dual` | ⚠️ maybe | Use `hermDual` instead (sorry-free) |

**Conclusion**: Everything we'd want to use is either sorry-free or has a sorry-free alternative.

### HermitianMat/ (4 total sorries)

All 4 are in CFC.lean, in advanced operator inequality proofs. None on our critical path.

### ForMathlib/ (0 sorries)

Completely sorry-free. The spectrum_prod and sharedEigenbasis results are fully proved.

---

## 9. Specific Items to Port/Rewrite — Prioritized List

### Priority 1: Week 1-2 (Foundation)

**Goal**: Prove `transferMap` is a CPTP map.

Port/rewrite from Unbundled.lean (~200 lines):
1. `IsCompletelyPositive` definition
2. `of_kraus_CP` — Kraus operators → CP
3. `of_kraus_isTracePreserving` — TP condition
4. `of_kraus_isCompletelyPositive` — full CP proof

This immediately gives us:
```lean
theorem transferMap_is_CP : IsCompletelyPositive (transferMap A) := of_kraus_CP A
theorem transferMap_is_TP (h : ∑ i, A i† * A i = 1) : IsTracePreserving (transferMap A) := ...
```

### Priority 2: Week 3-4 (Choi Matrix)

Port/rewrite from MatrixMap.lean (~200 lines):
1. `choi_matrix` definition
2. `of_choi_matrix` and inverse theorems
3. `toMatrix` — the transfer matrix T = Σ Aᵢ⊗Āᵢ

Port/rewrite from ForMathlib/Matrix.lean (~100 lines):
4. Key PSD lemmas for Choi matrix
5. `spectrum_prod` if needed

### Priority 3: Week 5-6 (Vectorization Bridge)

New code, using insights from Lean-QuantumInfo:
1. Vectorization: Mat(D×D) → Vec(D²) transforming E_A → multiplication by T
2. T = Σ Aᵢ⊗Āᵢ is entry-wise nonneg (from PSD structure of Choi)
3. Connect CP map eigenvalues to T eigenvalues

### Priority 4: Week 7-10 (Spectral Theory — THE HARD PART)

Entirely new code:
1. Show T has spectral radius 1 (from TP + PSD)
2. Define irreducibility for CP maps
3. Bridge to HopfieldNet's classical PF
4. Extract spectral gap
5. Prove block separation lemma

---

## 10. Key Mathematical Insight

The central mathematical bridge is:

```
E_A is a CPTP map  [Lean-QuantumInfo provides framework]
       ↓
Its Choi matrix T = Σ Aᵢ⊗Āᵢ is PSD  [Choi's theorem]
       ↓
T has nonneg entries (in computational basis)  [PSD + special structure]
       ↓
T is a nonneg matrix with spectral radius = ‖E_A‖_∞ = 1  [TP condition]
       ↓
If E_A is irreducible, T is a primitive nonneg matrix  [irreducibility bridge]
       ↓
Classical PF applies to T  [HopfieldNet provides this!]
       ↓
T has unique dominant eigenvalue 1, spectral gap > 0  [PF theorem]
       ↓
E_A^N → projector onto fixed point space  [convergence]
       ↓
Block separation: off-diagonal blocks of E_A^N vanish  [our goal]
```

Steps 1-3 are supported by Lean-QuantumInfo. Step 6 by HopfieldNet. Steps 4-5 and 7-8 are the genuine new mathematics we must formalize.

---

## 11. Comparison with Other Resources

| Resource | What it provides | Lean/Mathlib version | Integration |
|----------|-----------------|---------------------|-------------|
| **HopfieldNet** | Classical PF (stochastic matrices) | **Exact match** (v4.27.0, same Mathlib) | Lake dependency ✅ |
| **Lean-QuantumInfo** | CP maps, Choi, Kraus | v4.24.0 (3 behind) | Port/rewrite ⚠️ |
| **Mathlib** | CompletelyPositiveMap (minimal), Matrix basics | v4.27.0 (our version) | Already imported ✅ |
| **Nothing else** | No quantum PF exists in Lean anywhere | — | Must build ❌ |

---

## 12. Final Recommendations

1. **Import HopfieldNet as Lake dependency** — zero friction, maximum value
2. **Guided rewrite** of ~400-600 lines of CP map basics from Lean-QuantumInfo
3. **Do NOT attempt to import Lean-QuantumInfo directly** — version gap is too large
4. **Focus 80% of effort on the bridge** (vectorization + irreducibility + PF application)
5. **Consider reaching out to Alex Meiburg** — potential collaboration on version bump
6. **Total timeline**: ~10 weeks median, ~1,500 new lines
7. **Risk**: The irreducibility bridge (Step 5 above) is the highest-risk component — if the real representation argument doesn't work cleanly in Lean, may need an alternative proof strategy

---

## Appendix A: Complete File Inventory with Metrics

| # | File Path | Lines | Defs | Thms | Sorries | Relevance |
|---|-----------|-------|------|------|---------|-----------|
| 1 | CPTPMap/MatrixMap.lean | 390 | 12 | 15 | 2 | **CRITICAL** |
| 2 | CPTPMap/Unbundled.lean | 757 | 5 | 30+ | 1 | **CRITICAL** |
| 3 | CPTPMap/Bundled.lean | 435 | 9 | 10+ | 0 | **HIGH** |
| 4 | CPTPMap/CPTP.lean | 528 | 15+ | 10+ | 7 | MEDIUM |
| 5 | CPTPMap/Dual.lean | 505 | 5 | 15+ | 3 | MEDIUM |
| 6 | HermitianMat/Basic.lean | 371 | 10+ | 10+ | 0 | MEDIUM |
| 7 | HermitianMat/CFC.lean | 698 | 5+ | 15+ | 4 | LOW-MED |
| 8 | HermitianMat/CfcOrder.lean | 294 | 0 | 10+ | 0 | LOW |
| 9 | HermitianMat/Inner.lean | 500 | 5+ | 20+ | 0 | MEDIUM |
| 10 | HermitianMat/Jordan.lean | 151 | 1 | 5+ | 0 | LOW |
| 11 | HermitianMat/Log.lean | 646 | 3+ | 15+ | 0 | LOW |
| 12 | HermitianMat/Order.lean | 137 | 0 | 5+ | 0 | MEDIUM |
| 13 | HermitianMat/Proj.lean | 281 | 3+ | 10+ | 0 | LOW-MED |
| 14 | HermitianMat/Reindex.lean | 86 | 2 | 3 | 0 | LOW |
| 15 | HermitianMat/Trace.lean | 152 | 1 | 5+ | 0 | LOW |
| 16 | ForMathlib/Matrix.lean | 1,342 | 10+ | 40+ | 0 | **HIGH** |
| 17 | ForMathlib/Isometry.lean | 633 | 5+ | 15+ | 0 | **HIGH** |
| 18 | MState.lean | 1,441 | 15+ | 40+ | 0 | LOW |
| 19 | Pinching.lean | 587 | 5+ | 15+ | 0 | MEDIUM |
| 20 | Entropy.lean | 467 | 5+ | 10+ | 18 | NONE |
| 21 | Capacity.lean | 259 | 5+ | 5+ | 6 | NONE |
| 22 | TraceNorm.lean | 116 | 2 | 3 | 7 | NONE |
| 23 | POVM.lean | 244 | 5+ | 5+ | 7 | NONE |
| 24 | Measurement.lean | 269 | 5+ | 5+ | 11 | NONE |

## Appendix B: Every Key Theorem and Its Sorry Status

### Sorry-Free Theorems We Want
- `choi_PSD_iff_CP_map` ✅ — Choi's theorem
- `exists_kraus_of_choi_PSD` ✅ — Kraus decomposition
- `of_kraus_CP` ✅ — Kraus → CP
- `of_kraus_isTracePreserving` ✅ — TP condition
- `of_kraus_isCompletelyPositive` ✅ — Full CP from Kraus
- `choi_equiv` ✅ — Choi isomorphism
- `map_choi_inv` / `choi_map_inv` ✅ — Isomorphism inverses
- `kron_comp_distrib` ✅ — Tensor distributes over composition
- `kron_map_of_kron_state` ✅ — Tensor product on product states
- `spectrum_prod` ✅ — Spectrum of A⊗B
- `sharedEigenbasis` ✅ — Simultaneous diagonalization
- `pinching_map` ✅ — Pinching is CPTP
- `pinching_idempotent` ✅ — Pinching is idempotent
- `pinching_commutes` ✅ — Pinching output commutes with reference

### Sorry-Containing Theorems (with workarounds)
- `Dual.trace_eq` (1 sorry) → Use `hermDual` + `inner_hermDual` instead
- `IsHP.dual` (1 sorry) → Use `MatrixMap.IsPositive.hermDual` instead  
- `IsPos.dual` (1 sorry) → Use sorry-free alternative path

---

*End of Report*
