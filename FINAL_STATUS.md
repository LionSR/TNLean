# MPSLean — Project Status

## Summary

**~4,950 lines · 35 files · 0 axioms · 2 sorry (isolated helpers)**

The **Fundamental Theorem of Matrix Product States** is formalized:
- **Single-block case**: fully proved (0 sorry)
- **Multi-block case**: proved modulo per-block separation (taken as hypothesis)
- **Spectral gap theorem**: proved with 2 isolated helper sorry
  (both requiring doubly-stochastic gauge infrastructure)

## Build

```bash
lake build   # Lean 4 v4.27.0, Mathlib v4.27.0
# 0 axioms, 2 sorry warnings (private helpers in SpectralGap.lean), 0 errors
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

### Layer 5: Spectral Gap + Eigenvalue Rigidity ✅ (modulo 2 helper sorry)
- `eigenvalue_norm_le_one`: every eigenvalue of F_{AB} has modulus ≤ 1
- `spectralRadius_mixedTransfer_le_one`: ρ(F_{AB}) ≤ 1 for normalized tensors
- `modulus_one_eigenvalue_implies_gauge`: ρ(F_{AB}) ≥ 1 → gauge-phase equivalence (**was axiom, now theorem**)
- `eigenvector_gives_gauge`: **assembly proved** (no sorry) — chains Steps 1+2 + GL construction
- `spectralRadius_mixedTransfer_lt_one`: strict spectral gap for non-equivalent blocks
- `pow_tendsto_zero_of_spectralRadius_lt_one`: Gelfand formula convergence
- `cross_correlation_tendsto_zero`: mixed transfer iterates vanish

## Remaining Sorry (2)

Two **private helper lemmas** in `MPSLean/Spectral/SpectralGap.lean`, decomposed from
a single sorry at `eigenvector_gives_gauge` (whose assembly is fully proved):

| # | Line | Lemma | Mathematical Content |
|---|------|-------|---------------------|
| 1 | ~448 | `eigenvector_det_ne_zero` | F_{AB}(X) = μX, X ≠ 0, \|μ\| = 1 → X invertible |
| 2 | ~472 | `per_index_from_eigenvector` | F_{AB}(X) = μX, X invertible, \|μ\| = 1 → Bᵢ = μ̄ X⁻¹AᵢX |

### Proof Structure (sorry decomposition)

```
eigenvector_gives_gauge [PROVED — assembly, no sorry]
├── eigenvector_det_ne_zero [sorry — needs DS gauge for kernel invariance]
│   └── ker_X_all_of_inj [PROVED] → det_ne_zero_of_ker_all [PROVED]
│       (reduces to: show ker(X) is B†-invariant)
├── per_index_from_eigenvector [sorry — needs DS gauge for ∑‖Cᵢ‖²=D]
│   └── sum_conj_mul_conjTranspose [PROVED] → each_zero_of_sum_conjTranspose_mul_self_zero [PROVED]
│       (reduces to: show ∑‖Cᵢ‖²_F = D)
└── GL construction via Matrix.nonsingInvUnit [PROVED — by rfl]
```

### Required Infrastructure (not yet formalized)

Both sorry require the **doubly-stochastic gauge** construction:
1. Conjugate A by σ^{1/2} where σ is the QPF fixed point of E_A
2. The gauged channel is **unital** (∑A'ᵢA'ᵢ† = I, from E_A(σ)=σ)
3. Apply **Kadison-Schwarz equality** (tight HS contraction from |μ|=1)
4. This forces X to be in the **multiplicative domain**, giving both:
   - Kernel invariance (Step 1)
   - Per-index intertwining (Step 2)

The matrix square root infrastructure (σ^{1/2} = U·diag(√λ)) already exists in
`QPF/Uniqueness.lean` (`sqrtΛ'`, `sqrtFactor_mul_conjTranspose'`, etc.).
The remaining gap is ~200-300 lines connecting the gauge construction to the
Kadison-Schwarz equality condition.

**Alternative**: PGVWC OBC intertwiner approach (quant-ph/0608197, Lemma 5).

**References**:
- Wolf 2012, §6.2 (doubly-stochastic gauge + multiplicative domain)
- Pérez-García et al. 2007, Lemma 5 (OBC intertwiner approach)

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
