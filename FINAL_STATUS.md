# MPSLean — Project Status

## Summary

**~5,000 lines · 36 files · 0 axioms · 2 sorry (isolated helpers, assembly proved)**

The **Fundamental Theorem of Matrix Product States** is formalized:
- **Single-block case**: fully proved (0 sorry)
- **Multi-block case**: proved modulo per-block separation (taken as hypothesis)
- **Spectral gap theorem**: proved with 2 isolated helper sorry
  (assembly proved; helpers require multiplicative domain theory)

## Build

```bash
lake build   # Lean 4 v4.27.0, Mathlib v4.27.0
# 0 axioms, 2 sorry warnings (eigenvector_det_ne_zero, per_index_from_eigenvector), 0 errors
# Assembly (eigenvector_gives_gauge) is fully proved — no sorry
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
- `hilbertSchmidt_contraction` / `hilbertSchmidt_contraction_adjoint`: HS norm contraction

### Layer 5: Spectral Gap + Eigenvalue Rigidity ✅ (modulo 1 sorry)
- `eigenvalue_norm_le_one`: every eigenvalue of F_{AB} has modulus ≤ 1
- `spectralRadius_mixedTransfer_le_one`: ρ(F_{AB}) ≤ 1 for normalized tensors
- `modulus_one_eigenvalue_implies_gauge`: ρ(F_{AB}) ≥ 1 → gauge-phase equivalence
- `spectralRadius_mixedTransfer_lt_one`: strict spectral gap for non-equivalent blocks
- `pow_tendsto_zero_of_spectralRadius_lt_one`: Gelfand formula convergence
- `cross_correlation_tendsto_zero`: mixed transfer iterates vanish

### Layer 6: Doubly-Stochastic Gauge (partial) ✅
- `gauged_unital`: DS gauge unitality — `∑ (S⁻¹AᵢS)(S⁻¹AᵢS)† = I`
  when `S*S† = ρ` and `E_A(ρ) = ρ` (0 sorry)

## Remaining Sorry (2)

Two **private helper lemmas** in `MPSLean/Spectral/SpectralGap.lean`.
Their assembly (`eigenvector_gives_gauge`) is **fully proved** (no sorry).

| # | Line | Lemma | Mathematical Content |
|---|------|-------|---------------------|
| 1 | ~441 | `eigenvector_det_ne_zero` | F_{AB}(X) = μX, X ≠ 0, \|μ\| = 1 → X invertible |
| 2 | ~461 | `per_index_from_eigenvector` | F_{AB}(X) = μX, X invertible, \|μ\| = 1 → Bᵢ = μ̄ X⁻¹AᵢX |

### Proof Structure

```
eigenvector_gives_gauge [PROVED — assembly, no sorry]
├── eigenvector_det_ne_zero [sorry — needs multiplicative domain for kernel invariance]
│   └── ker_X_all_of_inj [PROVED] → det_ne_zero_of_ker_all [PROVED]
│       (reduces to: show ker(X) is B†-invariant)
├── per_index_from_eigenvector [sorry — needs ∑‖Cᵢ‖²=D from multiplicative domain]
│   └── sum_conj_mul_conjTranspose [PROVED] → each_zero_of_sum_conjTranspose_mul_self_zero [PROVED]
│       (reduces to: show ∑‖Cᵢ‖²_F = D)
└── GL construction via Matrix.nonsingInvUnit [PROVED — by rfl]
```

### Required Infrastructure (not yet formalized, ~200–500 lines)

Both sorry require the **multiplicative domain theory** for CP maps:

1. **Kadison–Schwarz equality**: `E(X†X) = E(X)†E(X)` iff X is in the
   multiplicative domain. For peripheral eigenvectors with `|μ| = 1`,
   the KS inequality becomes tight, placing X in the multiplicative domain.

2. **Multiplicative domain → kernel invariance** (Step 1): In the DS gauge
   (unitality proved in `gauged_unital`), the KS equality forces kernel invariance.

3. **Multiplicative domain → HS norm tightness** (Step 2): The equality
   `∑‖Cᵢ‖² = D` follows from multiplicative domain membership.

4. **Note**: The "TP direction" of the DS gauge (`∑(A'ᵢ)†A'ᵢ = I`) is NOT needed
   and does NOT hold in general. The proof uses multiplicative domain theory directly.

**Alternative**: PGVWC OBC intertwiner approach (quant-ph/0608197, Lemma 5).

**References**:
- Wolf 2012, §6.2 (multiplicative domain + peripheral eigenvalues)
- Pérez-García et al. 2007, Lemma 5 (OBC intertwiner approach)

## Architecture

```
MPSLean/
├── Algebra/         — TracePairing, TraceNondeg, SkolemNoether, BlockPermutation
├── Channel/         — PositiveMap, KadisonSchwarz, DSGauge, CesaroFixedPoint,
│                      Irreducible, Ergodic, Primitive, PeripheralSpectrum
├── MPS/             — Defs, Transfer, LinearExtension, CPPrimitive, CanonicalForm,
│                      BasisNormal, FundamentalTheorem, FundamentalTheoremMulti,
│                      BlockPermutationMPS, MultiBlock
├── PiAlgebra/       — Construction, BlockSeparation, FundamentalTheoremComplete
├── QPF/             — PosDef, Uniqueness
├── Spectral/        — MixedTransfer, CrossCorrelation, SpectralGap
└── QuantumPerronFrobenius.lean
```
