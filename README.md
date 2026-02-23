# TNLean

A formal verification of the **Fundamental Theorem of Matrix Product States** and the **Quantum Wielandt Bound** in Lean 4, using [Mathlib](https://github.com/leanprover-community/mathlib4) v4.27.0.

## Overview

[Matrix Product States](https://en.wikipedia.org/wiki/Matrix_product_state) (MPS) — equivalently, Tensor Networks with one-dimensional geometry — are a central tool in quantum information theory and condensed matter physics. The **Fundamental Theorem of MPS** states that two MPS tensors generating the same family of quantum states must be related by a gauge transform. The **Quantum Wielandt Bound** gives a constructive bound on the length needed for products of matrices to span the full algebra.

This project formalizes both results, following:

> - J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) (2020), Rev. Mod. Phys. **93**, 045003 (2021) — Fundamental Theorem of MPS
> - M. Sanz, D. Pérez-García, M. M. Wolf, J. I. Cirac, [arXiv:0909.5347](https://arxiv.org/abs/0909.5347) (2010), J. Math. Phys. **51**, 102205 — Quantum Wielandt Bound

## Project Statistics

| Metric | Value |
|--------|-------|
| Lean modules | 72 |
| Total lines of Lean | ~18,100 |
| Theorems / lemmas | 531 |
| Definitions | 92 |
| `sorry` in build target | 0 |
| `axiom` | 0 |
| Mathlib version | v4.27.0 |

## Main Results

### Single-Block Fundamental Theorem

```lean
theorem fundamentalTheorem_singleBlock {A B : MPSTensor d D}
    (hA : IsInjective A) (hAB : SameMPV A B) : GaugeEquiv A B
```

If an MPS tensor `A` is *injective* (its matrices span the full matrix algebra) and `B` generates the same MPV family, then `B i = X * A i * X⁻¹` for some invertible `X`.

### Multi-Block Fundamental Theorem

```lean
theorem fundamentalTheorem_multiBlock_full
    (hA : ∀ k, IsInjective (A k)) (hSame : SameMPV₂ μ A μ B) ... :
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)
```

The full multi-block result: block-diagonal MPS tensors with the same MPVs are globally gauge equivalent, handling block permutations, proportional eigenvalues, and spectral separation.

### Pi-Algebra Fundamental Theorem

```lean
theorem fundamentalTheorem_canonicalForm_sameStructure
    (C₁ C₂ : CanonicalForm d) (hC₁ : C₁.AllBlocksInjective)
    (hSame : SameMPV C₁.toTensor C₂.toTensor) ... :
    C₁.numBlocks = C₂.numBlocks ∧ ...
```

Two canonical-form MPS tensors with the same MPVs have the same block structure (number of blocks, dimensions up to permutation) and are related by a block-permuting gauge transform.

### Quantum Wielandt Bound

```lean
theorem cumulative_wielandt_bound [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    cumulativeSpan A (D ^ 2) = ⊤
```

For a normal MPS tensor, products of its matrices of length at most `D²` span the full matrix algebra `M_D(ℂ)`.

### Quantum Perron–Frobenius Theory

```lean
theorem IsChannel.exists_posSemidef_fixedPoint
    (hE : IsChannel E) (hD : 0 < D) :
    ∃ ρ, ρ.PosSemidef ∧ ρ ≠ 0 ∧ E ρ = ρ
```

Every quantum channel has a nonzero positive semidefinite fixed point (Cesàro mean / Markov–Kakutani argument).

## Directory Structure

```
TNLean/
├── Algebra/          8 files   1,391 lines   Pure linear/matrix algebra
│   ├── TracePairing, SkolemNoether, BlockPermutation, GramMatrixLI,
│   │   NewtonGirard, ScalarPowerSumIdentity, BlockTriangularTrace,
│   │   ProjectionTriangularTrace
├── Channel/          9 files   2,155 lines   Quantum channels (CPTP maps)
│   ├── PositiveMap, KadisonSchwarz, Schwarz, CesaroFixedPoint,
│   │   Irreducible, Primitive, PeripheralSpectrum, DSGauge,
│   │   MultiplicativeDomain
├── QPF/              3 files     745 lines   Quantum Perron–Frobenius
│   ├── PosDef, Uniqueness, Assembly
├── Spectral/         8 files   2,938 lines   Transfer operator spectral theory
│   ├── MixedTransfer, MPVOverlapTrace, SpectralGap, MPVOverlapDecay,
│   │   SpectralGapRect, PrimitiveOverlap, CrossCorrelation, TraceExpansion
├── MPS/             25 files   6,294 lines   MPS-specific theory & FT
│   ├── Defs, Transfer, LinearExtension, FundamentalTheorem,
│   │   FundamentalTheoremProportional, FundamentalTheoremFull,
│   │   FundamentalTheoremMulti, MultiBlock, BasisNormal, BNT,
│   │   BNTPermutationSimple, BNTPermutationThm44, BNTConstruction,
│   │   Blocking, MPVOverlap, CPPrimitive, InvariantSubspaceDecomp,
│   │   CanonicalFormReduction, IrreducibleFormII, BlockPermutationMPS,
│   │   CastLemmas, CoefficientConvergence, PrimitivityBridge,
│   │   TransferNormalization, FixedPointInvariantProjection
├── PiAlgebra/        5 files   1,951 lines   Pi-algebra multi-block infrastructure
│   ├── Construction, FundamentalTheoremComplete, BlockSeparation,
│   │   BlockSeparationProof, CanonicalFormSep
├── Wielandt/         7 files   1,954 lines   Quantum Wielandt bound
│   ├── CumulativeSpan, NonzeroTraceProduct, FittingDecomposition,
│   │   EigenvectorSpreading, RankOneProducts, WielandtBound,
│   │   PrimitivityNormal
└── Root files        4 files      95 lines   Re-export hubs
```

## Proof Architecture

The formalization is organized in layers:

**Layer 0 — General Algebra** (8 modules)
Trace pairing, Skolem–Noether theorem, block permutations of pi-algebras, Gram matrix linear independence, Newton–Girard identities.

**Layer 1 — Quantum Channels** (9 modules)
Positive maps, Kadison–Schwarz inequality, Cesàro fixed-point theorem, irreducibility, primitivity, peripheral spectrum characterization.

**Layer 2 — Quantum Perron–Frobenius + Spectral Theory** (11 modules)
Existence/uniqueness of PSD fixed points, transfer operators, spectral gap analysis, MPV overlap trace formulas, cross-correlation decay.

**Layer 3 — MPS Core + Fundamental Theorem** (25 modules)
MPS definitions, single-block FT (trace nondegeneracy → linear extension → multiplicativity → Skolem–Noether), proportional MPV extension, multi-block assembly, BNT (basis normal tensors) decomposition, invariant subspace decomposition, canonical form reduction.

**Layer 4 — Pi-Algebra + Block Separation** (5 modules)
Automorphisms of `∏ M_{D_k}(ℂ)` = block permutation + per-block inner automorphisms, block separation from spectral gap, complete fundamental theorem for canonical forms.

**Layer 5 — Quantum Wielandt Bound** (7 modules)
Cumulative span growth, Fitting decomposition, eigenvector spreading, rank-one products, Wielandt bound `D²`, primitivity ↔ normality bridge.

## Building

```bash
# Install elan (Lean version manager) if needed
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build
lake build
```

Requires Lean 4 v4.27.0 (managed via `lean-toolchain`).

## References

- J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) — Fundamental Theorem of MPS
- M. Sanz, D. Pérez-García, M. M. Wolf, J. I. Cirac, [arXiv:0909.5347](https://arxiv.org/abs/0909.5347) — Quantum Wielandt Bound
- M. M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012) — Positive map spectral theory
- M. Fannes, B. Nachtergaele, R. F. Werner, Commun. Math. Phys. **144**, 443–490 (1992) — Finitely correlated states
- [Mathlib4](https://github.com/leanprover-community/mathlib4) — Lean 4 mathematics library
