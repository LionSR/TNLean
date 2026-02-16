# MPSLean — Project Status

## Summary

**~4,900 lines · 35 files · 0 axioms · 1 sorry**

The **Fundamental Theorem of Matrix Product States** is formalized:
- **Single-block case**: fully proved (0 sorry)
- **Multi-block case**: proved modulo per-block separation (taken as hypothesis)
- **Spectral gap theorem**: proved with 1 private helper sorry (algebraic core of eigenvalue rigidity)

## Build

```bash
lake build   # Lean 4 v4.27.0, Mathlib v4.27.0
# 0 axioms, 1 sorry warning (private helper in SpectralGap.lean), 0 errors
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

### Layer 5: Spectral Gap + Eigenvalue Rigidity ✅ (modulo 1 private helper)
- `eigenvalue_norm_le_one`: every eigenvalue of F_{AB} has modulus ≤ 1
- `spectralRadius_mixedTransfer_le_one`: ρ(F_{AB}) ≤ 1 for normalized tensors
- `modulus_one_eigenvalue_implies_gauge`: ρ(F_{AB}) ≥ 1 → gauge-phase equivalence (**was axiom, now theorem**)
- `spectralRadius_mixedTransfer_lt_one`: strict spectral gap for non-equivalent blocks
- `pow_tendsto_zero_of_spectralRadius_lt_one`: Gelfand formula convergence
- `cross_correlation_tendsto_zero`: mixed transfer iterates vanish

## Remaining Sorry (1)

One **private helper lemma** in `MPSLean/Spectral/SpectralGap.lean`:

| # | Line | Lemma | Mathematical Content |
|---|------|-------|---------------------|
| 1 | ~467 | `eigenvector_gives_gauge` | F_{AB}(X) = μX, X ≠ 0, \|μ\| = 1, A,B injective normalized → GaugePhaseEquiv A B |

This is the algebraic core of the eigenvalue rigidity theorem. The proof requires:
- **Doubly-stochastic gauge**: conjugation by σ^{1/2} where σ is the QPF fixed point
- **Kadison-Schwarz equality ⟺ multiplicative domain**: tight HS contraction forces per-index intertwining
- Alternative: **PGVWC OBC approach** (Lemma 5, quant-ph/0608197)

Four fully proved helper lemmas (`ker_X_all_of_inj`, `det_ne_zero_of_ker_all`,
`sum_conj_mul_conjTranspose`, `each_zero_of_sum_conjTranspose_mul_self_zero`)
provide infrastructure that reduces the problem to:
- (a) showing ker(X) is B†-invariant (→ X invertible), and
- (b) deriving the per-index relation B_i = μ̄ X⁻¹ A_i X.

The mathematical content follows from standard functional analysis
(Wolf 2012, §6.2; Pérez-García et al. 2007, Lemma 5).
The formalization gap requires ~200-500 lines of new infrastructure
(doubly-stochastic gauge + multiplicative domain characterization).

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
