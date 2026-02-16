# MPSLean — Project Status

## Summary

**~5,000 lines · 36 files · 0 axioms · 1 sorry**

The **Fundamental Theorem of Matrix Product States** is formalized:
- **Single-block case**: fully proved (0 sorry)
- **Multi-block case**: proved modulo per-block separation (taken as hypothesis)
- **Spectral gap theorem**: proved with 1 isolated sorry
  (requires doubly-stochastic gauge + multiplicative domain infrastructure)

## Build

```bash
lake build   # Lean 4 v4.27.0, Mathlib v4.27.0
# 0 axioms, 1 sorry warning (eigenvector_gives_gauge in SpectralGap.lean), 0 errors
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

## Remaining Sorry (1)

A single **private lemma** in `MPSLean/Spectral/SpectralGap.lean`:

| Line | Lemma | Mathematical Content |
|------|-------|---------------------|
| ~480 | `eigenvector_gives_gauge` | F_{AB}(X) = μX, X ≠ 0, \|μ\| = 1, A,B injective normalized → GaugePhaseEquiv A B |

### Proof Decomposition (documented in docstring)

The proof has two major steps, each with fully proved helper lemmas that
reduce the problem to specific sub-goals:

**Step 1 — X is invertible**: Needs ker(X) to be B†-invariant.
- `ker_X_all_of_inj` [PROVED]: B†-kernel invariance → total kernel invariance
- `det_ne_zero_of_ker_all` [PROVED]: total kernel invariance + X ≠ 0 → det(X) ≠ 0
- **Gap**: showing ker(X) is B†-invariant (requires multiplicative domain theory)

**Step 2 — Per-index relation** (Bᵢ = μ̄ X⁻¹AᵢX):
- `sum_conj_mul_conjTranspose` [PROVED]: eigenvector eq + X invertible → ∑ CᵢBᵢ† = μI
- `each_zero_of_sum_conjTranspose_mul_self_zero` [PROVED]: ∑ Rᵢ†Rᵢ = 0 → Rᵢ = 0
- **Gap**: showing tr(∑ Cᵢ†Cᵢ) = D (requires doubly-stochastic gauge with TP condition)

**Assembly** (GL construction via `Matrix.nonsingInvUnit`): trivial once Steps 1+2 hold.

### Required Infrastructure (not yet formalized)

Both steps require infrastructure from the theory of **quantum channels with
peripheral eigenvalues** (~200–500 lines of new formalization):

1. **Multiplicative domain theory**: Kadison–Schwarz equality characterizes when
   `E(X†X) = E(X)†E(X)` holds. Peripheral eigenvectors lie in the multiplicative
   domain, which is a *-subalgebra. This gives kernel invariance (Step 1) and
   the HS norm tightness (Step 2).

2. **Doubly-stochastic gauge TP direction**: showing `∑ (A'ᵢ)†A'ᵢ = I` requires
   `E†_A(σ⁻¹) = σ⁻¹`, which does NOT hold for general primitive CPTP maps
   (counterexample: diagonal Kraus operators with unequal fixed point eigenvalues).
   The correct approach uses multiplicative domain theory directly, bypassing
   the need for the full DS gauge.

3. **Alternative**: The PGVWC OBC intertwiner approach (quant-ph/0608197, Lemma 5)
   uses parent Hamiltonian theory instead of channel analysis.

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
