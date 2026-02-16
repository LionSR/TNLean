# MPSLean — Project Status

## Summary

**~4,900 lines · 35 files · 0 axioms · 2 sorries**

The **Fundamental Theorem of Matrix Product States** is formalized:
- **Single-block case**: fully proved (0 sorry)
- **Multi-block case**: proved modulo per-block separation (taken as hypothesis)
- **Spectral gap theorem**: proved with 2 private helper sorry (algebraic core of eigenvalue rigidity)

## Build

```bash
lake build   # Lean 4 v4.27.0, Mathlib v4.27.0
# 0 axioms, 2 sorry warnings (both private helpers in SpectralGap.lean), 0 errors
```

## Completed Results

### Layer 1: Single-Block Fundamental Theorem ✅
- `fundamentalTheorem_singleBlock`: SameMPV + injective → GaugeEquiv (0 sorry)
- Proof: trace nondeg → linear extension → multiplicativity → Skolem–Noether

### Layer 2: Multi-Block Assembly ✅
- `fundamentalTheorem_multiBlock_global`: per-block SameMPV → global GaugeEquiv (0 sorry)
- MPV decomposition, Vandermonde separation, gauge assembly

### Layer 3: Block Permutation + Pi-Algebra ✅
- `algEquiv_pi_matrix_decomposition`: automorphisms of ∏ M_{D_k}(ℂ) = permutation + inner (0 sorry)
- `sameMPV₂_single_block`: r=1 case fully closed (0 sorry)
- `fundamentalTheorem_multiBlock_fromSameMPV₂`: end-to-end pipeline (0 sorry, given separation)

### Layer 4: Quantum Perron–Frobenius ✅
- `IsChannel.exists_posSemidef_fixedPoint`: every channel has PSD fixed point (Cesàro mean)
- `injective_implies_irreducibleCP`: injectivity → irreducibility
- `quantum_perron_frobenius`: unique PSD fixed point for injective tensors
- `kadison_schwarz` / `kadison_schwarz_adjoint`: Kadison–Schwarz inequality for CP maps

### Layer 5: Spectral Gap + Eigenvalue Rigidity ✅ (modulo 2 private helpers)
- `eigenvalue_norm_le_one`: every eigenvalue of F_{AB} has modulus ≤ 1
- `spectralRadius_mixedTransfer_le_one`: ρ(F_{AB}) ≤ 1 for normalized tensors
- `modulus_one_eigenvalue_implies_gauge`: ρ(F_{AB}) ≥ 1 → gauge-phase equivalence (**was axiom, now theorem**)
- `spectralRadius_mixedTransfer_lt_one`: strict spectral gap for non-equivalent blocks
- `pow_tendsto_zero_of_spectralRadius_lt_one`: Gelfand formula convergence
- `cross_correlation_tendsto_zero`: mixed transfer iterates vanish

## Remaining Sorries (2)

Both are **private helper lemmas** in `MPSLean/Spectral/SpectralGap.lean`:

| # | Line | Lemma | Mathematical Content |
|---|------|-------|---------------------|
| 1 | 338 | `ker_eigenvector_invariant` | Kernel of eigenvector X is B†-invariant |
| 2 | 429 | `per_index_relation` | X invertible + eigenvector equation → B_i = μ̄ X⁻¹ A_i X |

These are the algebraic core of the eigenvalue rigidity theorem. Their proofs require:
- **Sorry 1**: Kadison–Schwarz equality condition / multiplicative domain theory (doubly-stochastic gauge)
- **Sorry 2**: Trace argument via QPF fixed points and Cauchy–Schwarz tightness on Frobenius norm

Both follow from standard functional analysis (Wolf 2012, §6.2; Pérez-García et al. 2007, Lemma 5).
The mathematical content is well-understood; the formalization gap is purely technical.

## Architecture

```
MPSLean/
├── Algebra/         — TracePairing, TraceNondeg, SkolemNoether, Vandermonde
├── Channel/         — PositiveMap, KadisonSchwarz, CesaroFixedPoint, Irreducible
├── MPS/             — Defs, LinearExtension, CPPrimitive, FundamentalTheoremSingle
├── PiAlgebra/       — Construction, BlockSeparation, FundamentalTheoremComplete
├── QPF/             — PosDef, Uniqueness
├── Spectral/        — MixedTransfer, SpectralGap
└── QuantumPerronFrobenius.lean
```
